/-
Copyright (c) 2021 The UNSAT Group. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luke Nelson, Xi Wang
-/
import data.domain.basic
import data.domain.bv
import bpf.basic
import misc.with_top

namespace absint

/--
Class for abstractions of values of BPF registers.
-/
class value_abstr (α : Type*) extends
  has_γ bpf.value α,
  has_decidable_γ bpf.value α,
  abstr_le bpf.value α,
  abstr_top bpf.value α,
  abstr_join bpf.value α α :=

(doALU (op : bpf.ALU) :
  abstr_binary_transfer op.doALU α α α)

(doALU_check (op : bpf.ALU) :
  abstr_binary_test (λ x y, op.doALU_check x y = tt) α α)

(doJMP_check (op : bpf.JMP) :
  abstr_binary_test (λ x y, op.doJMP_check x y = tt) α α)

(doJMP_tt (op : bpf.JMP) :
  abstr_binary_inversion (λ x y, op.doJMP x y = tt) α α (with_bot α) (with_bot α))

(is_scalar : abstr_unary_test (λ (x : bpf.value), x.is_scalar) α)

(const (v : bpf.value) : abstr_nullary_relation (= v) α)

(unknown_scalar :
  abstr_nullary_relation (λ (x : bpf.value), x.is_scalar) α)

inductive avalue (β : Type) : Type
| scalar  : β → avalue
| pointer : bpf.memregion → β → avalue
| uninitialized : avalue

namespace avalue

variables {β : ℕ → Type} [bv_abstr β]

section has_repr
variables [has_repr (β 64)]

private def repr' : avalue (β 64) → string
| (scalar x) := "(scalar " ++ repr x ++ ")"
| (pointer _ o) := "(pointer X " ++ repr o ++ ")"
| uninitialized := "(uninitialized)"

instance : has_repr (avalue (β 64)) := ⟨repr'⟩

end has_repr

section has_to_pexpr
variable [has_to_pexpr (β 64)]

private meta def to_pexpr' : avalue (β 64) → pexpr
| (scalar x)      := ``(scalar %%x)
| (pointer m x)   := ``(pointer %%m %%x)
| (uninitialized) := ``(uninitialized)

meta instance : has_to_pexpr (avalue (β 64)) := ⟨to_pexpr'⟩

end has_to_pexpr

private def γ : avalue (β 64) → bpf.value → Prop
| (avalue.scalar x) (bpf.value.scalar y) := y ∈ has_γ.γ x
| (avalue.pointer m₁ x) (bpf.value.pointer m₂ y) :=
  m₁ = m₂ ∧ y ∈ has_γ.γ x
| (avalue.uninitialized) (bpf.value.uninitialized) := true
| _ _ := false

private def dec_γ : Π (a : avalue (β 64)) (b : bpf.value), decidable (γ a b) :=
begin
  intros a b,
  cases a; cases b; simp only [γ]; apply_instance
end

instance : has_γ bpf.value (avalue (β 64)) :=
{ γ := γ }

instance : has_decidable_γ bpf.value (avalue (β 64)) :=
{ dec_γ := dec_γ }

private def const (v : bpf.value) :
  abstr_nullary_relation (= v) (avalue (β 64)) :=
{ op :=
    match v with
    | (bpf.value.scalar x)      := (avalue.scalar (bv_abstr.const x).op)
    | (bpf.value.pointer m x)   := (avalue.pointer m (bv_abstr.const x).op)
    | (bpf.value.uninitialized) := (avalue.uninitialized)
    end,
  correct := by {
    intros x _,
    subst_vars,
    cases x,
    { apply (bv_abstr.const x).correct rfl },
    { refine ⟨rfl, _⟩,
      apply (bv_abstr.const _).correct rfl },
    { triv } } }

private def le : avalue (β 64) → avalue (β 64) → Prop
| (avalue.scalar x) (avalue.scalar y) := x ≤ y
| (avalue.pointer m₁ x) (avalue.pointer m₂ y) :=
  m₁ = m₂ ∧ x ≤ y
| (avalue.uninitialized) (avalue.uninitialized) := true
| _ _ := false

private def dec_le : Π (a b : avalue (β 64)), decidable (le a b) :=
begin
  intros a b,
  cases a; cases b; simp only [le]; apply_instance
end

instance : abstr_le bpf.value (avalue (β 64)) :=
{ le         := le,
  dec_le     := dec_le,
  le_correct := by {
    intros x y h₁ val h₂,
    cases x; cases val; try{cases h₂};
    cases y; try{cases h₁},
    { apply abstr_le.le_correct h₁ h₂, },
    { subst_vars,
      refine ⟨rfl, _⟩,
      apply abstr_le.le_correct; assumption },
    { triv } } }

instance avalue_join : abstr_join bpf.value (avalue (β 64)) (with_top (avalue (β 64))) :=
{ join := λ (x y : avalue (β 64)),
    match x, y with
    | avalue.scalar x', avalue.scalar y' := some $ avalue.scalar (x' ⊔ y')
    | avalue.pointer m₁ x', avalue.pointer m₂ y' :=
      if m₁ = m₂
      then pure $ avalue.pointer m₁ (x' ⊔ y')
      else ⊤
    | avalue.uninitialized, avalue.uninitialized := some avalue.uninitialized
    | _, _ := ⊤
    end,
  join_correct := by {
    intros x y val h₁,
    cases x; cases y; cases h₁; cases val; try{cases h₁}; simp only [avalue_join._match_1],
    { apply abstr_join.join_correct, left, exact h₁ },
    { apply abstr_join.join_correct, right, exact h₁ },
    { split_ifs; subst_vars,
      refine ⟨rfl, _⟩,
      apply abstr_join.join_correct, left, assumption,
      apply abstr_top.top_correct },
    { split_ifs; subst_vars,
      refine ⟨rfl, _⟩,
      apply abstr_join.join_correct, right, assumption,
      apply abstr_top.top_correct } } }

private def doALU_scalar : Π (op : bpf.ALU), abstr_binary_transfer op.doALU_scalar (β 64) (β 64) (β 64)
| bpf.ALU.ADD  := bv_abstr.add
| bpf.ALU.SUB  := bv_abstr.sub
| bpf.ALU.NEG  :=
  { op      := λ x _, bv_abstr.neg.op x,
    correct := by { intros, apply bv_abstr.neg.correct; assumption } }
| bpf.ALU.MUL  := bv_abstr.mul
| bpf.ALU.LSH  := bv_abstr.shl
| bpf.ALU.XOR  := bv_abstr.xor
| bpf.ALU.AND  := bv_abstr.and
| bpf.ALU.OR   := bv_abstr.or
| bpf.ALU.DIV  := bv_abstr.udiv
| bpf.ALU.MOD  := bv_abstr.urem
| bpf.ALU.RSH  := bv_abstr.lshr
| bpf.ALU.ARSH := bv_abstr.ashr
| _            := { op := λ _ _, ⊤, correct := by { intros, apply abstr_top.top_correct } }

private def doALU_scalar_pointer : Π (op : bpf.ALU) (m : bpf.memregion), abstr_binary_transfer (op.doALU_pointer_scalar m) (β 64) (β 64) (avalue (β 64))
| bpf.ALU.ADD m := {
  op := λ x y, avalue.pointer m (bv_abstr.add.op x y),
  correct := by {
    intros _ _ _ _ _ h₁ h₂ h,
    subst h,
    constructor,
    refl,
    apply bv_abstr.add.correct h₁ h₂ rfl } }
| bpf.ALU.SUB m := {
  op := λ x y, avalue.pointer m (bv_abstr.sub.op x y),
  correct := by {
    intros _ _ _ _ _ h₁ h₂ h,
    subst h,
    constructor,
    refl,
    apply bv_abstr.sub.correct h₁ h₂ rfl } }
| bpf.ALU.MUL m := {
  op := λ x y, avalue.pointer m x,
  correct := by {
    intros _ _ _ _ _ h₁ h₂ h,
    subst h,
    refine ⟨rfl, h₁⟩ } }
| bpf.ALU.DIV m := {
  op := λ x y, avalue.pointer m x,
  correct := by {
    intros _ _ _ _ _ h₁ h₂ h,
    subst h,
    refine ⟨rfl, h₁⟩ } }
| bpf.ALU.OR m := {
  op := λ x y, avalue.pointer m x,
  correct := by {
    intros _ _ _ _ _ h₁ h₂ h,
    subst h,
    refine ⟨rfl, h₁⟩ } }
| bpf.ALU.AND m := {
  op := λ x y, avalue.pointer m x,
  correct := by {
    intros _ _ _ _ _ h₁ h₂ h,
    subst h,
    refine ⟨rfl, h₁⟩ } }
| bpf.ALU.LSH m := {
  op := λ x y, avalue.pointer m x,
  correct := by {
    intros _ _ _ _ _ h₁ h₂ h,
    subst h,
    refine ⟨rfl, h₁⟩ } }
| bpf.ALU.RSH m := {
  op := λ x y, avalue.pointer m x,
  correct := by {
    intros _ _ _ _ _ h₁ h₂ h,
    subst h,
    refine ⟨rfl, h₁⟩ } }
| bpf.ALU.NEG m := {
  op := λ x y, avalue.pointer m x,
  correct := by {
    intros _ _ _ _ _ h₁ h₂ h,
    subst h,
    refine ⟨rfl, h₁⟩ } }
| bpf.ALU.MOD m := {
  op := λ x y, avalue.pointer m x,
  correct := by {
    intros _ _ _ _ _ h₁ h₂ h,
    subst h,
    refine ⟨rfl, h₁⟩ } }
| bpf.ALU.XOR m := {
  op := λ x y, avalue.pointer m x,
  correct := by {
    intros _ _ _ _ _ h₁ h₂ h,
    subst h,
    refine ⟨rfl, h₁⟩ } }
| bpf.ALU.MOV m := {
  op := λ x y, avalue.scalar y,
  correct := by {
    intros _ _ _ _ _ h₁ h₂ h,
    subst h,
    refine h₂ } }
| bpf.ALU.ARSH m := {
  op := λ x y, avalue.pointer m x,
  correct := by {
    intros _ _ _ _ _ h₁ h₂ h,
    subst h,
    refine ⟨rfl, h₁⟩ } }
| bpf.ALU.END m := {
  op := λ x y, avalue.pointer m x,
  correct := by {
    intros _ _ _ _ _ h₁ h₂ h,
    subst h,
    refine ⟨rfl, h₁⟩ } }

private def doALU (op : bpf.ALU) : abstr_binary_transfer op.doALU (avalue (β 64)) (avalue (β 64)) (with_top (avalue (β 64))) :=
{ op := λ (x y : avalue (β 64)),
    match x, y with
    | avalue.scalar x', avalue.scalar y' := some $ avalue.scalar $ (doALU_scalar op).op x' y'
    | avalue.pointer m x', avalue.scalar y' := some $ (doALU_scalar_pointer op m).op x' y'
    | _, src := if op = bpf.ALU.MOV then pure src else ⊤
    end,
  correct := by {
    intros _ _ _ _ _ h₁ h₂ h,
    subst h,
    cases u,
    case pointer : m x' {
      cases v,
      case pointer {
        simp only [doALU._match_1],
        split_ifs; subst_vars,
        simp only with match_simp,
        exact h₂,
        apply abstr_top.top_correct },
      case uninitialized {
        simp only [doALU._match_1],
        split_ifs; subst_vars,
        simp only with match_simp,
        exact h₂,
        apply abstr_top.top_correct },
      case scalar {
        simp only [doALU._match_1],
        cases x; try{cases h₁},
        cases y; try{cases h₂},
        subst_vars,
        simp only with match_simp,
        apply (doALU_scalar_pointer op _).correct; assumption <|> refl } },
    case uninitialized {
      simp only [doALU._match_1],
      split_ifs; subst_vars,
      simp only with match_simp,
      exact h₂,
      apply abstr_top.top_correct },
    cases x; try{cases h₁},
    cases v,
    case pointer {
      simp only [doALU._match_1],
      split_ifs; subst_vars,
      simp only with match_simp,
      exact h₂,
      apply abstr_top.top_correct },
    case uninitialized {
      simp only [doALU._match_1],
      split_ifs; subst_vars,
      simp only with match_simp,
      exact h₂,
      apply abstr_top.top_correct },
    cases y; try{cases h₂},
    simp only with match_simp,
    apply (doALU_scalar op).correct h₁ h₂ rfl } }

/--
Lift doALU to work on `with_top`. Specialize this because ALU.MOV can be made precise even when
one (or both) arguments are already ⊤, since MOV ⊤ src = src.
-/
private def doALU_with_top (op : bpf.ALU) : abstr_binary_transfer op.doALU (with_top (avalue (β 64))) (with_top (avalue (β 64))) (with_top (avalue (β 64))) :=
{ op := λ (x y : with_top (avalue (β 64))),
    match x, y with
    | some x, some y := (doALU op).op x y
    | _, src := if op = bpf.ALU.MOV then src else ⊤
    end,
  correct := by {
    intros _ _ _ _ _ h₁ h₂ h,
    subst h,
    cases u; cases v,
    { simp only [doALU_with_top._match_1],
      split_ifs; subst_vars,
      simp only with match_simp,
      apply abstr_top.top_correct },
    { simp only [doALU_with_top._match_1],
      split_ifs; subst_vars,
      simp only with match_simp,
      exact h₂,
      apply abstr_top.top_correct },
    { simp only [doALU_with_top._match_1],
      split_ifs; subst_vars,
      simp only with match_simp,
      apply abstr_top.top_correct },
    apply (doALU op).correct h₁ h₂ rfl } }

private def doALU_scalar_check : Π (op : bpf.ALU), abstr_binary_test (λ x y, op.doALU_scalar_check x y = tt) (β 64) (β 64)
| bpf.ALU.ADD := {
  test := λ _ _, tt,
  test_sound := by { intros, refl } }
| bpf.ALU.MOV := {
  test := λ _ _, tt,
  test_sound := by { intros, refl } }
| bpf.ALU.SUB := {
  test := λ _ _, tt,
  test_sound := by { intros, refl } }
| bpf.ALU.MUL := {
  test := λ _ _, tt,
  test_sound := by { intros, refl } }
| bpf.ALU.OR := {
  test := λ _ _, tt,
  test_sound := by { intros, refl } }
| bpf.ALU.AND := {
  test := λ _ _, tt,
  test_sound := by { intros, refl } }
| bpf.ALU.LSH := {
  test := λ _ _, ff,
  test_sound := by { intros, contradiction } }
| bpf.ALU.RSH := {
  test := λ _ _, ff,
  test_sound := by { intros, contradiction } }
| bpf.ALU.NEG := {
  test := λ _ _, tt,
  test_sound := by { intros, refl } }
| bpf.ALU.XOR := {
  test := λ _ _, tt,
  test_sound := by { intros, refl } }
| bpf.ALU.ARSH := {
  test := λ _ _, ff,
  test_sound := by { intros, contradiction } }
| bpf.ALU.END := {
  test := λ _ _, ff,
  test_sound := by { intros _ _ _ _ h, cases h } }
| bpf.ALU.DIV := {
  test := λ _ divisor, to_bool $ ¬ has_γ.γ divisor (0 : bpf.i64),
  test_sound := by {
    intros _ _ _ _ h₁ h₂ h₃,
    simp only [to_bool_iff] at h₁,
    simp only [bpf.ALU.doALU_scalar_check],
    contrapose! h₁,
    simp only [bnot_eq_true_eq_eq_ff, bool.to_bool_not, not_not, to_bool_ff_iff, ne.def, coe_sort_tt, iff_true, eq_iff_iff] at h₁,
    subst h₁,
    assumption } }
| bpf.ALU.MOD := {
  test := λ _ divisor, to_bool $ ¬ has_γ.γ divisor (0 : bpf.i64),
  test_sound := by {
    intros _ _ _ _ h₁ h₂ h₃,
    simp only [to_bool_iff] at h₁,
    simp only [bpf.ALU.doALU_scalar_check],
    contrapose! h₁,
    simp only [bnot_eq_true_eq_eq_ff, bool.to_bool_not, not_not, to_bool_ff_iff, ne.def, coe_sort_tt, iff_true, eq_iff_iff] at h₁,
    subst h₁,
    assumption } }

@[match_simp]
private def doALU_check_with_top (op : bpf.ALU) : Π (x y : with_top (avalue (β 64))), bool
| (some (avalue.scalar x)) (some (avalue.scalar y)) := (doALU_scalar_check op).test x y
| (some (avalue.pointer m x)) (some (avalue.scalar y)) := op.doALU_pointer_scalar_check
| _ (some (avalue.pointer _ _)) := if op = bpf.ALU.MOV then tt else ff
| _ (some (avalue.scalar _)) := if op = bpf.ALU.MOV then tt else ff
| _ _ := ff

@[match_simp]
private theorem doALU_check_with_top_none {op : bpf.ALU} {x : with_top (avalue (β 64))} :
  doALU_check_with_top op x none = ff :=
by cases x with x; try{cases x}; refl

@[match_simp]
private theorem doALU_check_with_top_uninitialized {op : bpf.ALU} {x : with_top (avalue (β 64))} :
  doALU_check_with_top op x (some uninitialized) = ff :=
by cases x with x; try{cases x}; refl

@[match_simp]
private theorem doALU_check_with_top_pointer {op : bpf.ALU} {x : with_top (avalue (β 64))} {m y} :
  doALU_check_with_top op x (some (avalue.pointer m y)) = if op = bpf.ALU.MOV then tt else ff :=
by cases x with x; try{cases x}; refl

private def doALU_check (op : bpf.ALU) : abstr_binary_test (λ x y, op.doALU_check x y = tt) (with_top (avalue (β 64))) (with_top (avalue (β 64))) :=
{ test := doALU_check_with_top op,
  test_sound := by {
    intros _ _ _ _ h₁ h₂ h₃,
    cases v with v',
    simp only with match_simp at h₁,
    { cases h₁ },
    { cases v',
      case pointer {
        simp only [and_true, eq_self_iff_true, if_false_right_eq_and, ite_eq_tt_distrib] with match_simp at h₁,
        subst h₁,
        cases y; try{cases h₃},
        simp only [if_true, eq_self_iff_true] with match_simp },
      case uninitialized {
        simp only with match_simp at h₁,
        cases h₁ },
      case scalar {
        cases u; try{cases h₁},
        case none {
          simp only [and_true, eq_self_iff_true, if_false_right_eq_and, ite_eq_tt_distrib] with match_simp at h₁,
          subst h₁,
          cases y; try{cases h₃},
          simp only with match_simp },
        case some {
          cases u,
          case scalar {
            simp only with match_simp at h₁,
            cases y; try{cases h₃},
            cases x; try{cases h₂},
            apply (doALU_scalar_check op).test_sound h₁ h₂ h₃ },
          case pointer {
            simp only [and_true, eq_self_iff_true, if_false_right_eq_and, ite_eq_tt_distrib] with match_simp at h₁,
            cases y; try{cases h₃},
            cases x; try{cases h₂},
            subst_vars,
            exact h₁ },
          case uninitialized {
            simp only [and_true, eq_self_iff_true, if_false_right_eq_and, ite_eq_tt_distrib] with match_simp at h₁,
            subst h₁,
            cases y; try{cases h₃},
            simp only with match_simp } } } } } }

private def doJMP_check (op : bpf.JMP) : abstr_binary_test (λ x y, op.doJMP_check x y = tt) (with_top (avalue (β 64))) (with_top (avalue (β 64))) :=
{ test := λ (x y : with_top (avalue (β 64))),
    match x, y with
    | some (avalue.scalar x), some (avalue.scalar y) := tt
    | _, _ := ff
    end,
  test_sound := by {
    intros _ _ _ _ h₁ h₂ h₃,
    cases u, cases h₁,
    cases v, cases u; cases h₁,
    cases u; cases v; cases h₁,
    cases x; try{cases h₂},
    cases y; try{cases h₃},
    refl } }

private def is_scalar : abstr_unary_test (λ (x : bpf.value), x.is_scalar) (with_top (avalue (β 64))) :=
{ test := λ (x : with_top (avalue (β 64))),
    match x with
    | some (avalue.scalar x) := tt
    | _ := ff
    end,
  test_sound := by {
    intros _ _ h₁ h₂,
    cases u,
    cases h₁,
    cases u; try{cases h₁},
    cases x; try{cases h₂},
    dunfold bpf.value.is_scalar,
    simp only [to_bool_true_eq_tt, coe_sort_tt, exists_eq'] } }

private def doJMP_tt (op : bpf.JMP) :
  abstr_binary_inversion (λ (x y : bpf.value), op.doJMP x y = tt)
    (with_top (avalue (β 64))) (with_top (avalue (β 64)))
    (with_bot (with_top (avalue (β 64)))) (with_bot (with_top (avalue (β 64)))) :=
abstr_binary_inversion.trivial

private def unknown_scalar : abstr_nullary_relation (λ (x : bpf.value), x.is_scalar) (with_top (avalue (β 64))) :=
{ op := some (avalue.scalar ⊤),
  correct := by {
    intros _ h,
    cases h,
    subst_vars,
    apply abstr_top.top_correct } }

instance : value_abstr (with_top (avalue (β 64))) :=
{ doALU          := doALU_with_top,
  const          := λ v, with_top.lift_nullary_relation (const v),
  doALU_check    := doALU_check,
  doJMP_check    := doJMP_check,
  is_scalar      := is_scalar,
  doJMP_tt       := doJMP_tt,
  unknown_scalar := unknown_scalar }

end avalue
end absint
