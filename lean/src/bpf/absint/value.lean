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

instance : abstr_le bpf.value (avalue β) :=
{ le         := le,
  dec_le     := by {
    intros x y,
    cases x with _ m₁ x; cases y with _ m₂ y,
    { simp only [le_iff, exists_false, or_false, exists_eq_right', exists_eq_right_right', and_false],
      apply_instance },
    { simp only [le_iff, exists_false, and_false, false_and, or_self],
      apply_instance },
    { simp only [le_iff, exists_false, or_false, exists_eq_right', exists_eq_right_right', and_false],
      apply_instance },
    { simp only [le_iff, false_or, exists_false, exists_and_distrib_left, and_false],
      by_cases m₁ = m₂,
      { subst h,
        by_cases x ≤ y,
        { apply decidable.is_true,
          tauto },
        { apply decidable.is_false,
          contrapose! h,
          rcases h with ⟨_, _, _, _, ⟨_, _⟩, ⟨_, _⟩⟩,
          subst_vars,
          assumption } },
      { apply decidable.is_false,
        contrapose! h,
        rcases h with ⟨_, _, _, _, ⟨_, _⟩, ⟨_, _⟩⟩,
        subst_vars } } },
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
      constructor,
      apply (doALU_scalar op).correct; assumption },
    all_goals { apply abstr_top.top_correct } } }

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

instance : value_abstr (with_top (avalue β)) :=
{ doALU       := λ op, with_top.lift_binary_transfer_arg (doALU op),
  doALU_check := sorry,
  doJMP_check := sorry,
  is_scalar   := is_scalar,
  doJMP_tt    := sorry }

end avalue
end absint
