/-
Copyright (c) 2021 The UNSAT Group. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luke Nelson, Xi Wang
-/
import bpf.basic
import smt.factory

namespace bpf
namespace cfg
namespace se
universe u

variables {β γ : Type u} [smt.factory β γ] [smt.add_factory β γ] [smt.const_factory β γ]
  [smt.eq_factory β γ] [smt.not_factory β γ] [smt.and_factory β γ] [smt.redor_factory β γ] [smt.ult_factory β γ]
  [smt.ule_factory β γ] [smt.slt_factory β γ] [smt.sle_factory β γ]
open smt.add_factory smt.const_factory smt.eq_factory smt.not_factory smt.and_factory smt.redor_factory smt.ult_factory
     smt.slt_factory smt.sle_factory smt.ule_factory factory.monad

/-- Symbolic values of BPF registers -/
inductive symvalue (β : Type u)
| pointer : bpf.memregion → β → symvalue
| scalar : β → symvalue
| unknown : erased value → symvalue

namespace symvalue

def is_scalar (x : symvalue β) : Prop :=
∃ r, x = scalar r

instance {x : symvalue β} : decidable (is_scalar x) :=
begin
  cases x,
  { refine decidable.is_false _,
    intro h, cases h, cases h_h },
  { refine decidable.is_true _,
    existsi x, refl },
  { refine decidable.is_false _,
    intro h, cases h, cases h_h }
end

inductive sat (g : γ) : (symvalue β) → bpf.value → Prop
| sat_pointer {r : bpf.memregion} {off : β} {off_v : bpf.i64} :
  factory.sat g off (⟨64, off_v⟩ : Σ (n : ℕ), fin n → bool) →
  sat (symvalue.pointer r off) (value.pointer r off_v)
| sat_scalar {val : β} {val_v : bpf.i64} :
  factory.sat g val (⟨64, val_v⟩ : Σ (n : ℕ), fin n → bool) →
  sat (symvalue.scalar val) (value.scalar val_v)
| sat_unknown {val : erased value} :
  sat (symvalue.unknown val) val.out

private theorem sat_of_le ⦃g g' : γ⦄ ⦃x : symvalue β⦄ ⦃v : value⦄ :
  g ≤ g' →
  sat g x v →
  sat g' x v :=
begin
  intros l sat₁,
  cases sat₁,
  case sat_pointer : _ _ _ sat' {
    exact sat.sat_pointer (factory.sat_of_le l sat') },
  case sat_scalar : _ _ sat' {
    exact sat.sat_scalar (factory.sat_of_le l sat') },
  case sat_unknown {
    cases sat₁,
    apply sat.sat_unknown }
end

private def denote_n (γ : Type u) [smt.factory β γ] (n : ℕ) (b : β) : erased (fin n → bool) := do
(v : Σ (n : ℕ), fin n → bool) ← factory.denote γ b,
match v with
| ⟨n', x⟩ := if h : n = n' then pure $ h.symm.rec_on x else default _
end

private def denote (γ : Type u) [smt.factory β γ] : symvalue β → erased value
| (scalar s)         := value.scalar <$> denote_n γ 64 s
| (pointer base off) := value.pointer base <$> denote_n γ 64 off
| (unknown v)        := v

private theorem denote_sound ⦃g : γ⦄ ⦃e : symvalue β⦄ ⦃x : value⦄ :
  sat g e x →
  denote γ e = erased.mk x :=
begin
  intros sat₁,
  cases sat₁,
  case sat_scalar : _ _ sat' {
    have h := factory.denote_sound sat',
    simp only [denote, denote_n, h, erased.out_mk, erased.bind_def, erased.bind_eq_out, erased.map_def],
    rw [dif_pos rfl],
    simp only [erased.map, erased.out_mk, erased.pure_def, erased.bind_eq_out] },
  case sat_pointer : _ _ _ sat' {
    have h := factory.denote_sound sat',
    simp only [denote, denote_n, h, erased.out_mk, erased.bind_def, erased.bind_eq_out, erased.map_def],
    rw [dif_pos rfl],
    simp only [erased.map, erased.out_mk, erased.pure_def, erased.bind_eq_out] },
  case sat_unknown {
    cases sat₁,
    simp only [denote, erased.mk_out] }
end

instance : factory bpf.value (symvalue β) γ :=
{ sat          := sat,
  sat_of_le    := sat_of_le,
  init_f       := factory.init_f (Σ (n : ℕ), fin n → bool) β,
  default      := ⟨symvalue.unknown $ erased.mk $ value.scalar 0⟩,
  denote       := denote γ,
  denote_sound := denote_sound }

def mk_scalar (imm : lsbvector 64) : state γ (symvalue β) :=
symvalue.scalar <$> mk_const imm

theorem le_mk_scalar {imm : lsbvector 64} : increasing (mk_scalar imm : state γ (symvalue β)) :=
begin
  apply increasing_map,
  apply le_mk_const
end

theorem sat_mk_scalar ⦃g g' : γ⦄ ⦃e₁ : symvalue β⦄ ⦃imm : lsbvector 64⦄ :
  (mk_scalar imm).run g = (e₁, g') →
  sat g' e₁ (bpf.value.scalar imm.nth) :=
begin
  intros mk,
  simp only [mk_scalar, state_t.run_map] at mk,
  cases mk,
  apply sat.sat_scalar,
  apply sat_mk_const,
  rw [prod.mk.eta]
end

def mk_unknown (v : erased value) : state γ (symvalue β) :=
pure (symvalue.unknown v)

theorem le_mk_unknown {v : erased value} : increasing (mk_unknown v : state γ (symvalue β)) :=
begin
  apply increasing_pure
end

theorem sat_mk_unknown ⦃g g' : γ⦄ ⦃e₁ : symvalue β⦄ ⦃v : erased bpf.value⦄ :
  (mk_unknown v).run g = (e₁, g') →
  sat g' e₁ v.out :=
begin
  intros mk,
  cases mk,
  constructor
end

-- /-- Lift a constant function on 64 bits to expressions, losing precision.
--     Computationally, this is just `mk_var`. -/
-- def lift2_denote (f : i64 → i64 → i64) (e₁ e₂ : β) : state γ β :=
-- mk_var $
-- (factory.denote γ e₁).bind (λ (v₁ : Σ n, fin n → bool),
--   (factory.denote γ e₂).bind (λ (v₂ : Σ n, fin n → bool),
--     erased.mk $
--       match v₁, v₂ with
--       | ⟨64, b₁⟩, ⟨64, b₂⟩ := f b₁ b₂
--       | _,        _        := default _
--       end))

-- def doALU : ∀ (op : bpf.ALU) (dst src : β), state γ β
-- | op dst src       := lift2_denote (bpf.ALU.doALU_scalar op) dst src

def doALU : Π (op : ALU) (a b : symvalue β), state γ (symvalue β)
| ALU.ADD (symvalue.scalar x) (symvalue.scalar y) :=
  symvalue.scalar <$> mk_add x y
| _ _ _ := pure (symvalue.unknown $ erased.mk $ value.scalar 0)

theorem doALU_increasing {op : ALU} {a b : symvalue β} : increasing (doALU op a b : state γ (symvalue β)) :=
sorry

theorem sat_doALU ⦃g g' : γ⦄ ⦃op : ALU⦄ ⦃e₁ e₂ e₃ : symvalue β⦄ ⦃v₁ v₂ : bpf.value⦄ :
  (doALU op e₁ e₂).run g = (e₃, g') →
  sat g  e₁ v₁ →
  sat g  e₂ v₂ →
  sat g' e₃ (bpf.ALU.doALU op v₁ v₂) :=
sorry

def doALU_check : Π (op : bpf.ALU) (a b : symvalue β), state γ β
| _ _ _ := mk_false

theorem doALU_check_increasing {op : ALU} {a b : symvalue β} : increasing (doALU_check op a b : state γ β) :=
sorry

theorem sat_doALU_check ⦃g g' : γ⦄ ⦃op : bpf.ALU⦄ ⦃e₁ e₂ : symvalue β⦄ ⦃e₃ : β⦄ ⦃v₁ v₂ : bpf.value⦄ :
  (doALU_check op e₁ e₂).run g = (e₃, g') →
  sat g e₁ v₁ →
  sat g e₂ v₂ →
  factory.sat g' e₃ (⟨1, λ _, bpf.ALU.doALU_check op v₁ v₂⟩ : Σ (n : ℕ), fin n → bool) :=
sorry

def doJMP : Π (op : JMP) (a b : symvalue β), state γ β
| JMP.JEQ  (symvalue.scalar x) (symvalue.scalar y) := mk_eq x y
| JMP.JNE  (symvalue.scalar x) (symvalue.scalar y) := mk_eq x y >>= mk_not
| JMP.JSET (symvalue.scalar x) (symvalue.scalar y) := mk_and x y >>= mk_redor
| JMP.JLT  (symvalue.scalar x) (symvalue.scalar y) := mk_ult x y
| JMP.JGT  (symvalue.scalar x) (symvalue.scalar y) := mk_ult y x
| JMP.JLE  (symvalue.scalar x) (symvalue.scalar y) := mk_ule x y
| JMP.JGE  (symvalue.scalar x) (symvalue.scalar y) := mk_ule y x
| JMP.JSLT (symvalue.scalar x) (symvalue.scalar y) := mk_slt x y
| JMP.JSGT (symvalue.scalar x) (symvalue.scalar y) := mk_slt y x
| JMP.JSLE (symvalue.scalar x) (symvalue.scalar y) := mk_sle x y
| JMP.JSGE (symvalue.scalar x) (symvalue.scalar y) := mk_sle y x
| _ _ _ := mk_true

theorem doJMP_increasing {op : JMP} {a b : symvalue β} : increasing (doJMP op a b : state γ β) :=
sorry

theorem sat_doJMP ⦃g g' : γ⦄ ⦃op : JMP⦄ ⦃e₁ e₂ : symvalue β⦄ ⦃e₃ : β⦄ ⦃v₁ v₂ : bpf.value⦄ :
  (doJMP op e₁ e₂).run g = (e₃, g') →
  sat g  e₁ v₁ →
  sat g  e₂ v₂ →
  factory.sat g' e₃ (⟨1, λ _, bpf.JMP.doJMP op v₁ v₂⟩ : Σ (n : ℕ), fin n → bool) :=
sorry

def doJMP_check : Π (op : JMP) (a b : symvalue β), state γ β
| _ (symvalue.scalar x) (symvalue.scalar y) := mk_true
| _ _ _ := mk_false

theorem doJMP_check_increasing {op : JMP} {a b : symvalue β} : increasing (doJMP_check op a b : state γ β) :=
sorry

theorem sat_doJMP_check ⦃g g' : γ⦄ ⦃op : JMP⦄ ⦃e₁ e₂ : symvalue β⦄ ⦃e₃ : β⦄ ⦃v₁ v₂ : bpf.value⦄ :
  (doJMP_check op e₁ e₂).run g = (e₃, g') →
  sat g e₁ v₁ →
  sat g e₂ v₂ →
  factory.sat g' e₃ (⟨1, λ _, bpf.JMP.doJMP_check op v₁ v₂⟩ : Σ (n : ℕ), fin n → bool) :=
sorry

end symvalue
end se
end cfg
end bpf
