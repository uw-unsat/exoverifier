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

namespace avalue

variables {β : Type} [bv_abstr 64 β]

section has_to_pexpr
variable [has_to_pexpr β]

private meta def to_pexpr' : avalue β → pexpr
| (scalar x)    := ``(scalar %%x)
| (pointer m x) := ``(pointer %%m %%x)

meta instance : has_to_pexpr (avalue β) := ⟨to_pexpr'⟩

end has_to_pexpr

@[mk_iff]
inductive γ : avalue β → bpf.value → Prop
| scalar {x y} :
  y ∈ has_γ.γ x →
  γ (avalue.scalar x) (bpf.value.scalar y)
| pointer {m x y} :
  y ∈ has_γ.γ x →
  γ (avalue.pointer m x) (bpf.value.pointer m y)

private def abstract : bpf.value → avalue β
| (bpf.value.scalar x)    := (avalue.scalar (has_γ.abstract x))
| (bpf.value.pointer m x) := (avalue.pointer m (has_γ.abstract x))

instance : has_decidable_γ bpf.value (avalue β) :=
{ γ     := γ,
  dec_γ := by {
    intros x y,
    cases x with _ m₁ x; cases y with _ m₂ y,
    { simp only [γ_iff, exists_false, or_false, exists_eq_right', exists_eq_right_right', and_false],
      apply has_decidable_γ.dec_γ },
    { simp only [γ_iff, exists_false, and_false, false_and, or_self],
      apply_instance },
    { simp only [γ_iff, exists_false, and_false, false_and, or_self],
      apply_instance },
    { simp only [γ_iff, false_or, exists_false, and_false],
      by_cases m₁ = m₂,
      { subst_vars,
        cases has_decidable_γ.dec_γ x y with h,
        case decidable.is_true {
          apply decidable.is_true,
          existsi [m₂, _, _, h],
          tauto },
        case decidable.is_false {
          apply decidable.is_false,
          contrapose! h,
          rcases h with ⟨_, _, _, _, ⟨_, _⟩, ⟨_, _⟩, ⟨_, _⟩⟩,
          subst_vars,
          assumption } },
       { apply decidable.is_false,
          contrapose! h,
          rcases h with ⟨_, _, _, _, ⟨_, _⟩, ⟨_, _⟩, ⟨_, _⟩⟩,
          subst_vars } } },
  abstract         := abstract,
  abstract_correct := by {
    intros x,
    cases x,
    { constructor,
      apply has_γ.abstract_correct },
    { constructor,
      apply has_γ.abstract_correct } } }

@[mk_iff]
inductive le : avalue β → avalue β → Prop
| scalar {x y : β} :
  x ≤ y →
  le (avalue.scalar x) (avalue.scalar y)
| pointer {x y : β} {m} :
  x ≤ y →
  le (avalue.pointer m x) (avalue.pointer m y)

private def dec_le : Π (a b : avalue β), decidable (le a b)
| (avalue.scalar x) (avalue.scalar y) :=
  if h : x ≤ y
  then decidable.is_true (le.scalar h)
  else decidable.is_false $ by {
    contrapose! h,
    cases h,
    assumption }
| (avalue.pointer m₁ x) (avalue.pointer m₂ y) :=
  if h : m₁ = m₂ ∧ x ≤ y
  then decidable.is_true $ by {
    cases h, subst_vars,
    constructor, assumption }
  else decidable.is_false $ by {
    contrapose! h,
    cases h, tauto }
| (avalue.scalar x) (avalue.pointer m y) :=
  decidable.is_false $ by { intros h, cases h }
| (avalue.pointer m x) (avalue.scalar y) :=
  decidable.is_false $ by { intros h, cases h }

instance : abstr_le bpf.value (avalue β) :=
{ le         := le,
  dec_le     := dec_le,
  le_correct := by {
    intros x y h₁ val h₂,
    cases x; cases y,
    { cases h₁,
      cases h₂,
      constructor,
      apply abstr_le.le_correct; assumption },
    { cases h₁ },
    { cases h₁ },
    { cases h₁,
      cases h₂,
      constructor,
      apply abstr_le.le_correct; assumption } } }

instance avalue_join : abstr_join bpf.value (avalue β) (with_top (avalue β)) :=
{ join := λ (x y : avalue β),
    match x, y with
    | avalue.scalar x', avalue.scalar y' := some $ avalue.scalar (x' ⊔ y')
    | avalue.pointer m₁ x', avalue.pointer m₂ y' :=
      if m₁ = m₂
      then pure $ avalue.pointer m₁ (x' ⊔ y')
      else ⊤
    | _, _ := ⊤
    end,
  join_correct := by {
    intros x y val h₁,
    cases x; cases y,
    { cases h₁; cases h₁; constructor; apply abstr_join.join_correct,
      { left, tauto },
      { right, tauto } },
    { simp only [avalue_join._match_1] },
    { simp only [avalue_join._match_1] },
    { simp only [avalue_join._match_1],
      split_ifs,
      { subst h,
        cases h₁; cases h₁; constructor; apply abstr_join.join_correct,
        { left, tauto },
        { right, tauto } },
      { apply abstr_top.top_correct } } } }

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
    | _, _ := ⊤
    end,
  correct := by {
    intros _ _ _ _ h₁ h₂,
    cases u; cases v,
    { cases h₁, cases h₂,
      simp only [bpf.ALU.doALU_scalar_def],
      constructor,
      apply (doALU_scalar op).correct; assumption },
    all_goals { apply abstr_top.top_correct } } }

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
      simp only [bpf.ALU.doALU_MOV_def],
      apply abstr_top.top_correct },
    { simp only [doALU_with_top._match_1],
      split_ifs; subst_vars,
      simp only [bpf.ALU.doALU_MOV_def],
      exact h₂,
      apply abstr_top.top_correct },
    { simp only [doALU_with_top._match_1],
      split_ifs; subst_vars,
      simp only [bpf.ALU.doALU_MOV_def],
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

private def doALU_check (op : bpf.ALU) : abstr_binary_test bpf.value (with_top (avalue β)) op.doALU_check :=
{ test := λ (x y : with_top (avalue β)),
    match x, y with
    | some (avalue.scalar x), some (avalue.scalar y) := (doALU_scalar_check op).test x y
    | _, _ := if op = bpf.ALU.MOV then tt else ff
    end,
  test_sound := by {
    intros _ _ _ _ h₁ h₂ h₃,
    cases u,
    simp only [doALU_check._match_1] at h₁,
    split_ifs at h₁; subst_vars,
    simp only [bpf.ALU.doALU_check_MOV_def],
    cases h₁,
    cases u, swap,
    simp only [doALU_check._match_1] at h₁,
    split_ifs at h₁; subst_vars,
    simp only [bpf.ALU.doALU_check_MOV_def],
    cases h₁,
    cases v,
    simp only [doALU_check._match_1] at h₁,
    split_ifs at h₁; subst_vars,
    simp only [bpf.ALU.doALU_check_MOV_def],
    cases h₁,
    cases v, swap,
    simp only [doALU_check._match_1] at h₁,
    split_ifs at h₁; subst_vars,
    simp only [bpf.ALU.doALU_check_MOV_def],
    cases h₁,    cases h₂ with _ _ h₂',
    cases h₃ with _ _ h₃',
    simp only [bpf.ALU.doALU_scalar_check_def],
    exact (doALU_scalar_check op).test_sound h₁ h₂' h₃' } }

private def doJMP_check (op : bpf.JMP) : abstr_binary_test bpf.value (with_top (avalue β)) op.doJMP_check :=
{ test := λ (x y : with_top (avalue β)),
    match x, y with
    | some (avalue.scalar x), some (avalue.scalar y) := tt
    | _, _ := ff
    end,
  test_sound := by {
    intros _ _ _ _ h₁ h₂ h₃,
    cases u, cases h₁,
    cases u, swap, cases h₁,
    cases v, cases h₁,
    cases v, swap, cases h₁,
    cases h₂ with _ _ h₂',
    cases h₃ with _ _ h₃',
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
    cases u,
    cases h₁,
    cases h₂,
    dunfold bpf.value.is_scalar,
    simp only [to_bool_true_eq_tt, exists_eq'],
    cases h₁ } }

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
