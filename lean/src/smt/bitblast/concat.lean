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

/-- Create a `concat` circuit. -/
def mk_concat : (Σ n, vector β n) → (Σ n, vector β n) → state γ (Σ n, vector β n)
| ⟨n₁, v₁⟩ ⟨n₂, v₂⟩ := pure ⟨n₂ + n₁, v₂.append v₁⟩

section
variable [sat.factory β γ]

@[priority 100] -- see Note [lower instance priority]
instance : smt.concat_factory (Σ (n : ℕ), vector β n) γ :=
{ mk_concat     := mk_concat,
  le_mk_concat  := by {
    intros,
    cases e₁, cases e₂,
    apply increasing_pure },
  sat_mk_concat := by {
    intros _ _ _ _ _ _ _ _ _ mk sat₁ sat₂,
    cases e₁ with n₁ e₁,
    cases e₂ with n₂ e₂,
    have c := eval.length_eq sat₁, simp only at c, subst c,
    simp only [mk_concat, state_t.run_pure] at mk,
    cases mk, clear mk,
    simp only [factory.sat],
    rw [sat.iff_forall₂, bv.list_of_fn_concat, vector.to_list_append],
    from list.rel_append sat₂ sat₁ } }

end
end bitblast
end smt
