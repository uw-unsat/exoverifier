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
  has_decidable_γ bpf.value α,
  abstr_le bpf.value α,
  abstr_top bpf.value α,
  abstr_join bpf.value α α :=

(doALU (op : bpf.ALU) :
  abstr_binary_transfer bpf.value α α op.doALU)

(doALU_check (op : bpf.ALU) :
  abstr_binary_test bpf.value α op.doALU_check)

(doJMP_check (op : bpf.JMP) :
  abstr_binary_test bpf.value α op.doJMP_check)

(doJMP_tt (op : bpf.JMP) :
  abstr_binary_inversion bpf.value α (with_bot α) (λ x y, op.doJMP x y = tt))

(is_scalar : abstr_unary_test bpf.value α (λ x, to_bool x.is_scalar))

inductive avalue (β : Type) : Type
| scalar  : β → avalue
| pointer : bpf.memregion → β → avalue
| uninitialized : avalue

namespace avalue

variables {β : Type} [bv_abstr 64 β]

section has_repr
variable [has_repr β]

private def repr' : avalue β → string
| (scalar x) := "(scalar " ++ repr x ++ ")"
| (pointer _ o) := "(pointer X " ++ repr o ++ ")"
| uninitialized := "(uninitialized)"

instance : has_repr (avalue β) := ⟨repr'⟩

end has_repr

section has_to_pexpr
variable [has_to_pexpr β]

private meta def to_pexpr' : avalue β → pexpr
| (scalar x)      := ``(scalar %%x)
| (pointer m x)   := ``(pointer %%m %%x)
| (uninitialized) := ``(uninitialized)

meta instance : has_to_pexpr (avalue β) := ⟨to_pexpr'⟩

end has_to_pexpr

private def γ : avalue β → bpf.value → Prop
| (avalue.scalar x) (bpf.value.scalar y) := y ∈ has_γ.γ x
| (avalue.pointer m₁ x) (bpf.value.pointer m₂ y) :=
  m₁ = m₂ ∧ y ∈ has_γ.γ x
| (avalue.uninitialized) (bpf.value.uninitialized) := true
| _ _ := false

private def dec_γ : Π (a : avalue β) (b : bpf.value), decidable (γ a b) :=
begin
  intros a b,
  cases a; cases b; simp only [γ]; apply_instance
end

private def abstract : bpf.value → avalue β
| (bpf.value.scalar x)      := (avalue.scalar (has_γ.abstract x))
| (bpf.value.pointer m x)   := (avalue.pointer m (has_γ.abstract x))
| (bpf.value.uninitialized) := (avalue.uninitialized)

instance : has_decidable_γ bpf.value (avalue β) :=
{ γ     := γ,
  dec_γ := dec_γ,
  abstract         := abstract,
  abstract_correct := by {
    intros x,
    cases x,
    { apply has_γ.abstract_correct },
    { refine ⟨rfl, _⟩,
      apply has_γ.abstract_correct },
    { triv } } }

private def le : avalue β → avalue β → Prop
| (avalue.scalar x) (avalue.scalar y) := x ≤ y
| (avalue.pointer m₁ x) (avalue.pointer m₂ y) :=
  m₁ = m₂ ∧ x ≤ y
| (avalue.uninitialized) (avalue.uninitialized) := true
| _ _ := false

private def dec_le : Π (a b : avalue β), decidable (le a b) :=
begin
  intros a b,
  cases a; cases b; simp only [le]; apply_instance
end

instance : abstr_le bpf.value (avalue β) :=
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

instance avalue_join : abstr_join bpf.value (avalue β) (with_top (avalue β)) :=
{ join := λ (x y : avalue β),
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

private def doALU_scalar : Π (op : bpf.ALU), abstr_binary_transfer bpf.i64 β β op.doALU_scalar
| bpf.ALU.ADD  := bv_abstr.add
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

private def doALU (op : bpf.ALU) : abstr_binary_transfer bpf.value (avalue β) (with_top (avalue β)) op.doALU :=
{ op := λ (x y : avalue β),
    match x, y with
    | avalue.scalar x', avalue.scalar y' := some $ avalue.scalar $ (doALU_scalar op).op x' y'
    | _, src := if op = bpf.ALU.MOV then pure src else ⊤
    end,
  correct := by {
    intros _ _ _ _ h₁ h₂,
    cases u,
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
    apply (doALU_scalar op).correct h₁ h₂ } }

/--
Lift doALU to work on `with_top`. Specialize this because ALU.MOV can be made precise even when
one (or both) arguments are already ⊤, since MOV ⊤ src = src.
-/
private def doALU_with_top (op : bpf.ALU) : abstr_binary_transfer bpf.value (with_top (avalue β)) (with_top (avalue β)) op.doALU :=
{ op := λ (x y : with_top (avalue β)),
    match x, y with
    | some x, some y := (doALU op).op x y
    | _, src := if op = bpf.ALU.MOV then src else ⊤
    end,
  correct := by {
    intros _ _ _ _ h₁ h₂,
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
    apply (doALU op).correct h₁ h₂ } }

private def doALU_scalar_check : Π (op : bpf.ALU), abstr_binary_test bpf.i64 β op.doALU_scalar_check
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
  test := λ _ _, tt,
  test_sound := by { intros, refl } }
| bpf.ALU.RSH := {
  test := λ _ _, tt,
  test_sound := by { intros, refl } }
| bpf.ALU.NEG := {
  test := λ _ _, tt,
  test_sound := by { intros, refl } }
| bpf.ALU.XOR := {
  test := λ _ _, tt,
  test_sound := by { intros, refl } }
| bpf.ALU.ARSH := {
  test := λ _ _, tt,
  test_sound := by { intros, refl } }
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
    simp only [bnot_eq_true_eq_eq_ff, bool.to_bool_not, not_not, to_bool_ff_iff, ne.def] at h₁,
    subst h₁,
    assumption } }
| bpf.ALU.MOD := {
  test := λ _ divisor, to_bool $ ¬ has_γ.γ divisor (0 : bpf.i64),
  test_sound := by {
    intros _ _ _ _ h₁ h₂ h₃,
    simp only [to_bool_iff] at h₁,
    simp only [bpf.ALU.doALU_scalar_check],
    contrapose! h₁,
    simp only [bnot_eq_true_eq_eq_ff, bool.to_bool_not, not_not, to_bool_ff_iff, ne.def] at h₁,
    subst h₁,
    assumption } }

@[match_simp]
private def doALU_check_with_top (op : bpf.ALU) : Π (x y : with_top (avalue β)), bool
| (some (avalue.scalar x)) (some (avalue.scalar y)) := (doALU_scalar_check op).test x y
| _ (some (avalue.pointer _ _)) := if op = bpf.ALU.MOV then tt else ff
| _ (some (avalue.scalar _)) := if op = bpf.ALU.MOV then tt else ff
| _ _ := ff

@[match_simp]
private theorem doALU_check_with_top_none {op : bpf.ALU} {x : with_top (avalue β)} :
  doALU_check_with_top op x none = ff :=
by cases x with x; try{cases x}; refl

@[match_simp]
private theorem doALU_check_with_top_uninitialized {op : bpf.ALU} {x : with_top (avalue β)} :
  doALU_check_with_top op x (some uninitialized) = ff :=
by cases x with x; try{cases x}; refl

@[match_simp]
private theorem doALU_check_with_top_pointer {op : bpf.ALU} {x : with_top (avalue β)} {m y} :
  doALU_check_with_top op x (some (avalue.pointer m y)) = if op = bpf.ALU.MOV then tt else ff :=
by cases x with x; try{cases x}; refl

private def doALU_check (op : bpf.ALU) : abstr_binary_test bpf.value (with_top (avalue β)) op.doALU_check :=
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
        { simp only [and_true, eq_self_iff_true, if_false_right_eq_and, ite_eq_tt_distrib] with match_simp at h₁,
          subst h₁,
          cases y; try{cases h₃},
          simp only with match_simp },
        { cases u,
          { simp only with match_simp at h₁,
            cases y; try{cases h₃},
            cases x; try{cases h₂},
            apply (doALU_scalar_check op).test_sound h₁ h₂ h₃ },
          { simp only [and_true, eq_self_iff_true, if_false_right_eq_and, ite_eq_tt_distrib] with match_simp at h₁,
            subst h₁,
            cases y; try{cases h₃},
            simp only with match_simp },
          { simp only [and_true, eq_self_iff_true, if_false_right_eq_and, ite_eq_tt_distrib] with match_simp at h₁,
            subst h₁,
            cases y; try{cases h₃},
            simp only with match_simp } } } } } }

private def doJMP_check (op : bpf.JMP) : abstr_binary_test bpf.value (with_top (avalue β)) op.doJMP_check :=
{ test := λ (x y : with_top (avalue β)),
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

private def is_scalar : abstr_unary_test bpf.value (with_top (avalue β)) (λ (x : bpf.value), to_bool x.is_scalar) :=
{ test := λ (x : with_top (avalue β)),
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
    simp only [to_bool_true_eq_tt, exists_eq'] } }

private def doJMP_tt (op : bpf.JMP) :
  abstr_binary_inversion bpf.value (with_top (avalue β)) (with_bot (with_top (avalue β)))
    (λ (x y : bpf.value), op.doJMP x y = tt) :=
abstr_binary_inversion.trivial

instance : value_abstr (with_top (avalue β)) :=
{ doALU       := doALU_with_top,
  doALU_check := doALU_check,
  doJMP_check := doJMP_check,
  is_scalar   := is_scalar,
  doJMP_tt    := doJMP_tt }

end avalue
end absint
