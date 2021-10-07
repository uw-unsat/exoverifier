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
     smt.slt_factory smt.sle_factory smt.ule_factory

/-- Symbolic values of BPF registers -/
inductive symvalue (β : Type u)
| pointer : bpf.memregion → β → symvalue
| scalar : β → symvalue
| unknown : erased value → symvalue

namespace symvalue

inductive sat (g : γ) : (symvalue β) → bpf.value → Prop
| sat_pointer {r : bpf.memregion} {off : β} {off_v : bpf.i64} :
  factory.sat g off (⟨64, off_v⟩ : Σ (n : ℕ), fin n → bool) →
  sat (symvalue.pointer r off) (value.pointer r off_v)
| sat_scalar {val : β} {val_v : bpf.i64} :
  factory.sat g val (⟨64, val_v⟩ : Σ (n : ℕ), fin n → bool) →
  sat (symvalue.scalar val) (value.scalar val_v)

instance : factory bpf.value (symvalue β) γ :=
{ sat          := sat,
  sat_of_le    := sorry,
  init_f       := factory.init_f (Σ (n : ℕ), fin n → bool) β,
  default      := ⟨symvalue.unknown $ erased.mk $ value.scalar 0⟩,
  denote       := sorry,
  denote_sound := sorry }

def mk_scalar (imm : lsbvector 64) : state γ (symvalue β) :=
symvalue.scalar <$> mk_const imm

theorem sat_mk_scalar ⦃g g' : γ⦄ ⦃e₁ : symvalue β⦄ ⦃imm : lsbvector 64⦄ :
  (mk_scalar imm).run g = (e₁, g') →
  sat g e₁ (bpf.value.scalar imm.nth) :=
sorry

def mk_unknown (v : erased value) : state γ (symvalue β) :=
pure (symvalue.unknown v)

theorem sat_mk_unknown ⦃g g' : γ⦄ ⦃e₁ : symvalue β⦄ ⦃v : erased bpf.value⦄ :
  (mk_unknown v).run g = (e₁, g') →
  sat g e₁ v.out :=
sorry

def doALU : Π (op : bpf.ALU) (a b : symvalue β), state γ (symvalue β)
| bpf.ALU.ADD (symvalue.scalar x) (symvalue.scalar y) :=
  symvalue.scalar <$> mk_add x y
| _ _ _ := pure (symvalue.unknown $ erased.mk $ value.scalar 0)

theorem sat_doALU ⦃g g' : γ⦄ ⦃op : bpf.ALU⦄ ⦃e₁ e₂ e₃ : symvalue β⦄ ⦃v₁ v₂ : bpf.value⦄ :
  (doALU op e₁ e₂).run g = (e₃, g') →
  sat g e₁ v₁ →
  sat g e₂ v₂ →
  sat g e₃ (bpf.ALU.doALU op v₁ v₂) :=
sorry

def doALU_check : Π (op : bpf.ALU) (a b : symvalue β), state γ β
| _ _ _ := mk_false

theorem sat_doALU_check ⦃g g' : γ⦄ ⦃op : bpf.ALU⦄ ⦃e₁ e₂ : symvalue β⦄ ⦃e₃ : β⦄ ⦃v₁ v₂ : bpf.value⦄ :
  (doALU_check op e₁ e₂).run g = (e₃, g') →
  sat g e₁ v₁ →
  sat g e₂ v₂ →
  factory.sat g e₃ (⟨1, λ _, bpf.ALU.doALU_check op v₁ v₂ = tt⟩ : Σ (n : ℕ), fin n → bool) :=
sorry

def doJMP : Π (op : bpf.JMP) (a b : symvalue β), state γ β
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

def doJMP_check : Π (op : bpf.JMP) (a b : symvalue β), state γ β
| _ (symvalue.scalar x) (symvalue.scalar y) := mk_true
| _ _ _ := mk_false

end symvalue
end se
end cfg
end bpf
