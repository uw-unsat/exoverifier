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

variables {β γ : Type u}
  [smt.factory β γ] [smt.extract_factory β γ] [smt.neg_factory β γ] [smt.add_factory β γ]
  [smt.and_factory β γ] [smt.const_factory β γ] [smt.eq_factory β γ] [smt.implies_factory β γ]
  [smt.redor_factory β γ] [smt.not_factory β γ] [smt.or_factory β γ] [smt.var_factory β γ]
  [smt.udiv_factory β γ] [smt.xor_factory β γ] [smt.sub_factory β γ] [smt.ult_factory β γ]
  [smt.mul_factory β γ] [smt.shl_factory β γ] [smt.lshr_factory β γ] [smt.ite_factory β γ]
  [smt.urem_factory β γ]

open smt.add_factory smt.const_factory smt.eq_factory smt.not_factory smt.and_factory smt.redor_factory smt.ult_factory
     smt.slt_factory smt.sle_factory smt.ule_factory factory.monad smt.var_factory smt.or_factory smt.udiv_factory smt.xor_factory
     smt.shl_factory smt.ashr_factory smt.lshr_factory smt.mul_factory smt.neg_factory smt.sub_factory smt.urem_factory

/-- Symbolic values of BPF registers -/
inductive symvalue (β : Type u)
| pointer : bpf.memregion → β → symvalue
| scalar : β → symvalue
| uninitialized : symvalue

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

abbreviation is_uninitialized (x : symvalue β) : Prop :=
x = uninitialized

inductive sat (g : γ) : (symvalue β) → bpf.value → Prop
| sat_pointer {r : bpf.memregion} {off : β} {off_v : bpf.i64} :
  factory.sat g off (⟨64, off_v⟩ : Σ (n : ℕ), fin n → bool) →
  sat (symvalue.pointer r off) (value.pointer r off_v)
| sat_scalar {val : β} {val_v : bpf.i64} :
  factory.sat g val (⟨64, val_v⟩ : Σ (n : ℕ), fin n → bool) →
  sat (symvalue.scalar val) (value.scalar val_v)
| sat_uninitialized :
  sat symvalue.uninitialized value.uninitialized

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
  case sat_uninitialized {
    constructor }
end

private def denote_n (γ : Type u) [smt.factory β γ] (n : ℕ) (b : β) : erased (fin n → bool) := do
(v : Σ (n : ℕ), fin n → bool) ← factory.denote γ b,
match v with
| ⟨n', x⟩ := if h : n = n' then pure $ h.symm.rec_on x else default _
end

private def denote (γ : Type u) [smt.factory β γ] : symvalue β → erased value
| (scalar s)         := value.scalar <$> denote_n γ 64 s
| (pointer base off) := value.pointer base <$> denote_n γ 64 off
| (uninitialized)    := pure bpf.value.uninitialized

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
  case sat_uninitialized {
    refl }
end

instance : factory bpf.value (symvalue β) γ :=
{ sat          := sat,
  sat_of_le    := sat_of_le,
  init_f       := factory.init_f (Σ (n : ℕ), fin n → bool) β,
  default      := ⟨symvalue.scalar $ (factory.default (Σ n, fin n → bool) γ).1⟩,
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

def mk_uninitialized : state γ (symvalue β) :=
pure symvalue.uninitialized

theorem le_mk_uninitialized : increasing (mk_uninitialized : state γ (symvalue β)) :=
by apply increasing_pure

theorem sat_mk_uninitialized ⦃g g' : γ⦄ ⦃e : symvalue β⦄ :
  mk_uninitialized.run g = (e, g') →
  sat g' e bpf.value.uninitialized :=
begin
  rintros ⟨⟩,
  constructor
end

private def doALU_scalar : Π (op : ALU) (a b : β), state γ β
| ALU.ADD  := mk_add
| ALU.AND  := mk_and
| ALU.ARSH := mk_ashr
| ALU.DIV  := mk_udiv
| ALU.END  := λ a _, pure a
| ALU.LSH  := mk_shl
| ALU.MOD  := mk_urem
| ALU.MOV  := λ _ y, pure y
| ALU.MUL  := mk_mul
| ALU.NEG  := λ x _, mk_neg x
| ALU.OR   := mk_or
| ALU.RSH  := mk_lshr
| ALU.SUB  := mk_sub
| ALU.XOR  := mk_xor

private theorem sat_doALU_scalar ⦃g g' : γ⦄ ⦃op : ALU⦄ ⦃e₁ e₂ e₃ : β⦄ ⦃v₁ v₂ : bpf.i64⦄ :
  (doALU_scalar op e₁ e₂).run g = (e₃, g') →
  factory.sat g e₁ (⟨64, v₁⟩ : Σ (n : ℕ), fin n → bool) →
  factory.sat g e₂ (⟨64, v₂⟩ : Σ (n : ℕ), fin n → bool) →
  factory.sat g' e₃ (⟨64, op.doALU_scalar v₁ v₂⟩ : Σ (n : ℕ), fin n → bool) :=
begin
  intros mk sat₁ sat₂,
  cases op,
  case ADD { exact sat_mk_add mk sat₁ sat₂ },
  case AND { exact sat_mk_and mk sat₁ sat₂ },
  case ARSH { exact sat_mk_ashr mk sat₁ sat₂ },
  case DIV { exact sat_mk_udiv mk sat₁ sat₂ },
  case END { cases mk, assumption },
  case LSH { exact sat_mk_shl mk sat₁ sat₂ },
  case MOD { exact sat_mk_urem mk sat₁ sat₂ },
  case MOV { cases mk, assumption },
  case MUL { exact sat_mk_mul mk sat₁ sat₂ },
  case NEG { exact sat_mk_neg mk sat₁ },
  case OR { exact sat_mk_or mk sat₁ sat₂ },
  case RSH { exact sat_mk_lshr mk sat₁ sat₂ },
  case SUB { exact sat_mk_sub mk sat₁ sat₂ },
  case XOR { exact sat_mk_xor mk sat₁ sat₂ }
end

@[match_simp]
private def doALU_pointer_scalar : Π (op : ALU) (m : bpf.memregion) (off val : β), state γ (symvalue β)
| ALU.ADD  m off val := symvalue.pointer m <$> (mk_add off val)
| ALU.SUB  m off val := symvalue.pointer m <$> (mk_sub off val)
| ALU.MOV  m off val := pure $ symvalue.scalar val
| _        m off _   := pure $ symvalue.pointer m off

private theorem sat_doALU_pointer_scalar ⦃g g' : γ⦄ ⦃op : ALU⦄ ⦃m : bpf.memregion⦄ ⦃e₁ e₂ : β⦄ ⦃v₁ v₂ : bpf.i64⦄ ⦃e₃ : symvalue β⦄ :
  (doALU_pointer_scalar op m e₁ e₂).run g = (e₃, g') →
  factory.sat g e₁ (⟨64, v₁⟩ : Σ (n : ℕ), fin n → bool) →
  factory.sat g e₂ (⟨64, v₂⟩ : Σ (n : ℕ), fin n → bool) →
  sat g' e₃ (op.doALU_pointer_scalar m v₁ v₂) :=
begin
  intros mk sat₁ sat₂,
  cases op; simp only [state_t.run_map] with match_simp at mk ⊢,
  case ADD {
    cases mk,
    apply sat.sat_pointer,
    apply sat_mk_add (by rw [prod.mk.eta]) sat₁ sat₂ },
  case SUB {
    cases mk,
    apply sat.sat_pointer,
    apply sat_mk_sub (by rw [prod.mk.eta]) sat₁ sat₂ },
  case MOV {
    cases mk,
    apply sat.sat_scalar sat₂ },
  all_goals {
    cases mk,
    apply sat.sat_pointer sat₁ }
end

@[match_simp]
def doALU : Π (op : ALU) (a b : symvalue β), state γ (symvalue β)
| op      (symvalue.scalar x)      (symvalue.scalar y)   := symvalue.scalar <$> doALU_scalar op x y
| op      (symvalue.pointer m off) (symvalue.scalar val) := doALU_pointer_scalar op m off val
| ALU.MOV _                        b                     := pure b
| _       a                        _                     := pure a

@[match_simp]
private theorem doALU_scalar_def {op : ALU} {x y : β} :
  (doALU op (symvalue.scalar x) (symvalue.scalar y) : state γ _) = symvalue.scalar <$> doALU_scalar op x y :=
by cases op; refl

@[match_simp]
private theorem doALU_pointer_scalar_def {op : ALU} {m} {x y : β} :
  (doALU op (symvalue.pointer m x) (symvalue.scalar y) : state γ _) = doALU_pointer_scalar op m x y :=
by cases op; refl

theorem doALU_increasing {op : ALU} {a b : symvalue β} : increasing (doALU op a b : state γ (symvalue β)) :=
begin
  cases a,
  case pointer {
    cases b,
    case pointer { cases op; simp only with match_simp; apply increasing_pure },
    case scalar {
      cases op; simp only with match_simp; try{apply increasing_pure},
      case ADD { apply increasing_map, apply le_mk_add },
      case SUB { apply increasing_map, apply le_mk_sub } },
    case uninitialized { cases op; apply increasing_pure } },
  case uninitialized {
    cases op; apply increasing_pure },

  cases b,
  case pointer {
    cases op; apply increasing_pure },
  case uninitialized {
    cases op; apply increasing_pure },

  cases op,
  case ADD { apply increasing_map, apply le_mk_add },
  case AND { apply increasing_map, apply le_mk_and },
  case ARSH { apply increasing_map, apply le_mk_ashr },
  case DIV { apply increasing_map, apply le_mk_udiv },
  case END { apply increasing_map, apply increasing_pure },
  case LSH { apply increasing_map, apply le_mk_shl },
  case MOD { apply increasing_map, apply le_mk_urem },
  case MOV { apply increasing_map, apply increasing_pure },
  case MUL { apply increasing_map, apply le_mk_mul },
  case NEG { apply increasing_map, apply le_mk_neg },
  case OR { apply increasing_map, apply le_mk_or },
  case RSH { apply increasing_map, apply le_mk_lshr },
  case SUB { apply increasing_map, apply le_mk_sub },
  case XOR { apply increasing_map, apply le_mk_xor }
end

theorem sat_doALU ⦃g g' : γ⦄ ⦃op : ALU⦄ ⦃e₁ e₂ e₃ : symvalue β⦄ ⦃v₁ v₂ : bpf.value⦄ :
  (doALU op e₁ e₂).run g = (e₃, g') →
  sat g  e₁ v₁ →
  sat g  e₂ v₂ →
  sat g' e₃ (bpf.ALU.doALU op v₁ v₂) :=
begin
  intros mk sat₁ sat₂,
  cases sat₁,
  case sat.sat_pointer {
    cases sat₂,
    case sat_pointer {
      cases op; cases mk; exact sat₁ <|> exact sat₂ },
    case sat_uninitialized {
      cases op; cases mk; exact sat₁ <|> exact sat₂ },
    case sat_scalar {
      simp only with match_simp at mk ⊢,
      apply sat_doALU_pointer_scalar mk,
      assumption,
      assumption } },
  case sat.sat_uninitialized {
    cases op; cases mk; exact sat₁ <|> exact sat₂ },

  cases sat₂,
  case sat.sat_pointer {
    cases op; cases mk; exact sat₁ <|> exact sat₂ },
  case sat.sat_uninitialized {
    cases op; cases mk; exact sat₁ <|> exact sat₂ },

  simp only [state_t.run_map] with match_simp at mk,
  cases mk,
  simp only with match_simp,
  constructor,
  apply sat_doALU_scalar,
  { rw prod.mk.eta },
  { assumption },
  { assumption }
end

private def doALU_scalar_check : Π (op : ALU) (a b : β), state γ β
| ALU.DIV _ y := mk_redor y
| ALU.MOD _ y := mk_redor y
| ALU.END _ _ := mk_false
| _       _ _ := mk_true

private def doALU_pointer_scalar_check : Π (op : ALU), state γ β
| ALU.ADD := mk_true
| ALU.SUB := mk_true
| ALU.MOV := mk_true
| _       := mk_false

@[match_simp]
def doALU_check : Π (op : ALU) (a b : symvalue β), state γ β
| op (symvalue.scalar x) (symvalue.scalar y) := doALU_scalar_check op x y
| op (symvalue.pointer m x) (symvalue.scalar y) := doALU_pointer_scalar_check op
| op _ (symvalue.scalar _) := if op = ALU.MOV then mk_true else mk_false
| op _ (symvalue.pointer _ _) := if op = ALU.MOV then mk_true else mk_false
| _ _ _ := mk_false

@[match_simp]
private theorem doALU_check_scalar_scalar_def {op : ALU} {x y : β} :
  (doALU_check op (symvalue.scalar x) (symvalue.scalar y) : state γ _) = doALU_scalar_check op x y :=
by cases op; refl

@[match_simp]
private theorem doALU_check_any_pointer_def {op : ALU} {a : symvalue β} {m} {y : β} :
  (doALU_check op a (symvalue.pointer m y) : state γ _) = if op = ALU.MOV then mk_true else mk_false :=
by cases op; cases a; refl

@[match_simp]
private theorem doALU_check_any_uninitialized_def {op : ALU} {a : symvalue β} :
  (doALU_check op a (symvalue.uninitialized) : state γ _) = mk_false :=
by cases op; cases a; refl

theorem doALU_check_increasing {op : ALU} {a b : symvalue β} : increasing (doALU_check op a b : state γ β) :=
begin
  cases a; cases b; simp only [doALU_check]; try{split_ifs}; try{apply le_mk_const};
  cases op; try{apply le_mk_const},
  apply le_mk_redor,
  apply le_mk_redor,
end

theorem sat_doALU_check ⦃g g' : γ⦄ ⦃op : bpf.ALU⦄ ⦃e₁ e₂ : symvalue β⦄ ⦃e₃ : β⦄ ⦃v₁ v₂ : bpf.value⦄ :
  (doALU_check op e₁ e₂).run g = (e₃, g') →
  sat g e₁ v₁ →
  sat g e₂ v₂ →
  factory.sat g' e₃ (⟨1, λ _, bpf.ALU.doALU_check op v₁ v₂⟩ : Σ (n : ℕ), fin n → bool) :=
begin
  intros mk sat₁ sat₂,
  cases sat₂,
  case sat.sat_pointer {
    simp only with match_simp at mk ⊢,
    split_ifs at ⊢ mk; apply sat_mk_const1 mk },
  case sat.sat_uninitialized {
    simp only with match_simp at mk ⊢,
    apply sat_mk_const1 mk },
  case sat.sat_scalar : _ _ sat₂' {
    cases sat₁,
    case sat.sat_pointer {
      simp only with match_simp at mk ⊢,
      cases op; apply sat_mk_const1 mk },
    case sat.sat_uninitialized {
      simp only with match_simp at mk ⊢,
      split_ifs at ⊢ mk; apply sat_mk_const1 mk },

    simp only with match_simp at mk ⊢,
    cases op;
    try {
      convert (sat_mk_const mk),
      ext i,
      simp only [fin.eq_zero i],
      refl };
    { convert (sat_mk_redor mk sat₂'),
      ext i,
      rw [bv.any_eq_to_bool_nonzero],
      refl } }
end

def doJMP_check : Π (op : JMP) (a b : symvalue β), state γ β
| _ (symvalue.scalar x) (symvalue.scalar y) := mk_true
| op a                   b                  := mk_false

theorem doJMP_check_increasing {op : JMP} {a b : symvalue β} : increasing (doJMP_check op a b : state γ β) :=
begin
  cases a; cases b; apply le_mk_const <|> apply le_mk_var
end

theorem sat_doJMP_check ⦃g g' : γ⦄ ⦃op : JMP⦄ ⦃e₁ e₂ : symvalue β⦄ ⦃e₃ : β⦄ ⦃v₁ v₂ : bpf.value⦄ :
  (doJMP_check op e₁ e₂).run g = (e₃, g') →
  sat g e₁ v₁ →
  sat g e₂ v₂ →
  factory.sat g' e₃ (⟨1, λ _, bpf.JMP.doJMP_check op v₁ v₂⟩ : Σ (n : ℕ), fin n → bool) :=
begin
  intros mk sat₁ sat₂,
  cases sat₁,
  case sat.sat_pointer {
    apply sat_mk_const1 mk },
  case sat.sat_uninitialized {
    apply sat_mk_const1 mk },
  case sat.sat_scalar : _ _ sat₁' {
    cases sat₂,
    case sat.sat_pointer {
      apply sat_mk_const1 mk },
    case sat.sat_uninitialized {
      apply sat_mk_const1 mk },
    case sat.sat_scalar : _ _ sat₂' {
      convert (sat_mk_const mk),
      ext i,
      simp only [fin.eq_zero i],
      refl } }
end

private def doJMP_scalar : Π (op : JMP) (a b : β), state γ β
| JMP.JEQ  x y := mk_eq x y
| JMP.JNE  x y := mk_eq x y >>= mk_not
| JMP.JSET x y := mk_and x y >>= mk_redor
| JMP.JLT  x y := mk_ult x y
| JMP.JGT  x y := mk_ult y x
| JMP.JLE  x y := mk_ule x y
| JMP.JGE  x y := mk_ule y x
| JMP.JSLT x y := mk_slt x y
| JMP.JSGT x y := mk_slt y x
| JMP.JSLE x y := mk_sle x y
| JMP.JSGE x y := mk_sle y x

def doJMP : Π (op : JMP) (a b : symvalue β), state γ β
| op (symvalue.scalar x) (symvalue.scalar y) := doJMP_scalar op x y
| op a                   b                   := mk_false

theorem doJMP_increasing {op : JMP} {a b : symvalue β} : increasing (doJMP op a b : state γ β) :=
begin
  cases a; try{apply le_mk_const},
  cases b; try{apply le_mk_const},
  cases op,
  case JEQ { apply le_mk_eq },
  case JNE {
    apply increasing_bind; intros,
    apply le_mk_eq,
    apply le_mk_not },
  case JSET {
    apply increasing_bind; intros,
    apply le_mk_and,
    apply le_mk_redor },
  case JLE { apply le_mk_ule },
  case JLT { apply le_mk_ult },
  case JGE { apply le_mk_ule },
  case JGT { apply le_mk_ult },
  case JSLE { apply le_mk_sle },
  case JSLT { apply le_mk_slt },
  case JSGE { apply le_mk_sle },
  case JSGT { apply le_mk_slt }
end

theorem sat_doJMP ⦃g g' : γ⦄ ⦃op : JMP⦄ ⦃e₁ e₂ : symvalue β⦄ ⦃e₃ : β⦄ ⦃v₁ v₂ : bpf.value⦄ :
  (doJMP op e₁ e₂).run g = (e₃, g') →
  sat g  e₁ v₁ →
  sat g  e₂ v₂ →
  factory.sat g' e₃ (⟨1, λ _, bpf.JMP.doJMP op v₁ v₂⟩ : Σ (n : ℕ), fin n → bool) :=
begin
  intros mk sat₁ sat₂,
  cases sat₁,
  case sat_pointer {
    apply sat_mk_const1 mk },
  case sat_uninitialized {
    apply sat_mk_const1 mk },
  case sat_scalar : _ _ sat₁' {

    cases sat₂,
    case sat_pointer {
      apply sat_mk_const1 mk },
    case sat_uninitialized {
      apply sat_mk_const1 mk },
    case sat_scalar : _ _ sat₂' {

      cases op,
      case JEQ {
        exact sat_mk_eq mk sat₁' sat₂' },
      case JLT {
        exact sat_mk_ult mk sat₁' sat₂' },
      case JLE {
        exact sat_mk_ule mk sat₁' sat₂' },
      case JGT {
        exact sat_mk_ult mk sat₂' sat₁' },
      case JGE {
        exact sat_mk_ule mk sat₂' sat₁' },
      case JSLT {
        exact sat_mk_slt mk sat₁' sat₂' },
      case JSLE {
        exact sat_mk_sle mk sat₁' sat₂' },
      case JSGT {
        exact sat_mk_slt mk sat₂' sat₁' },
      case JSGE {
        exact sat_mk_sle mk sat₂' sat₁' },
      case JNE {
        simp only [doJMP, doJMP_scalar, state_t.run_bind] at mk,
        convert (sat_mk_not mk (sat_mk_eq (by rw [prod.mk.eta]) sat₁' sat₂')),
        ext i,
        simp only [bpf.JMP.doJMP, bpf.JMP.doJMP_scalar, fin.eq_zero i, bv.not, bool.to_bool_not] },
      case JSET {
        simp only [doJMP, doJMP_scalar, state_t.run_bind] at mk,
        convert (sat_mk_redor mk (sat_mk_and (by rw [prod.mk.eta]) sat₁' sat₂')),
        ext i,
        simp only [bpf.JMP.doJMP, bpf.JMP.doJMP_scalar, bv.any_eq_to_bool_nonzero] } } }
end

end symvalue
end se
end cfg
end bpf
