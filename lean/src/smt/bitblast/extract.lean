/-
Copyright (c) 2021 The UNSAT Group. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luke Nelson, Xi Wang
-/
import .basic

universe u
variables {β γ : Type u}

namespace smt
namespace bitblast

open factory.monad

/-- Create an `extract` circuit. -/
def mk_extract (upper lower : ℕ) : (Σ n, vector β n) → state γ (Σ n, vector β n)
| ⟨n, v⟩ := pure ⟨_, (v.drop lower).take (upper - lower + 1)⟩

section
variable [sat.factory β γ]

@[priority 100] -- see Note [lower instance priority]
instance : smt.extract_factory (Σ (n : ℕ), vector β n) γ :=
{ mk_extract     := mk_extract,
  le_mk_extract  := by {
    intros,
    cases e,
    apply increasing_pure },
  sat_mk_extract := by {
    intros _ _ _ _ _ _ _ _ mk sat₁ h₁ h₂,
    simp only [factory.sat, sat] at sat₁,
    cases e₁ with n₁ e₁,
    cases e₂ with n₂ e₂,
    have c := eval.length_eq sat₁, simp only at c, subst c,
    simp only [mk_extract, state_t.run_pure] at mk,
    cases mk, clear mk,
    simp only [factory.sat],
    rw [sat.iff_forall₂, bv.list_of_fn_extract],
    cases e₁ with l₁ h₁,
    rw [vector.to_list_take],
    simp only [vector.to_list_drop, vector.to_list_take, vector.to_list_mk],
    apply list.forall₂_take,
    apply list.forall₂_drop,
    rw [eval.iff_forall₂] at sat₁,
    from sat₁ } }

end
end bitblast
end smt
