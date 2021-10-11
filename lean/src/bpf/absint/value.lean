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
  abstr_join bpf.value α α,
  abstr_meet bpf.value α (with_bot α) :=

(doALU (op : bpf.ALU) :
  abstr_binary_transfer bpf.value α α (bpf.ALU.doALU op))

(doJMP_tt (op : bpf.JMP) :
  abstr_binary_inversion bpf.value α (with_bot α) (λ x y, op.doJMP x y = tt))

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
    cases x; cases y; sorry },
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

instance : abstr_meet bpf.value (with_top (avalue β)) (with_bot (with_top (avalue β))) :=
sorry

instance : abstr_join bpf.value (avalue β) (with_top (avalue β)) := sorry

instance : value_abstr (with_top (avalue β)) :=
{ doALU := sorry,
  doJMP_tt := sorry }

end avalue
end absint
