/-
Copyright (c) 2021 The UNSAT Group. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luke Nelson, Xi Wang
-/
import .basic

universe u
variables {β γ : Type u} [sat.factory β γ]

namespace smt
namespace bitblast
variable [sat.not_factory β γ]

open factory.monad

/-- Create an n-bit NOT circuit. -/
def mk_not : ∀ {n : ℕ}, vector β n → state γ (vector β n) :=
mk_unary_bitwise_op sat.not_factory.mk_not

theorem le_mk_not {n : ℕ} {v : vector β n} {g : γ} :
  g ≤ ((mk_not v).run g).2 :=
begin
  apply le_mk_unary_bitwise_op,
  apply sat.not_factory.le_mk_not
end

theorem eval_mk_not {n : ℕ} {g g' : γ} {v₁ v₂ : vector β n} {b₁ : fin n → bool} :
  (mk_not v₁).run g = (v₂, g') →
  eval g v₁ b₁ →
  eval g' v₂ (bv.not b₁) :=
begin
  apply eval_mk_unary_bitwise_op,
  { apply sat.not_factory.le_mk_not },
  { intros _ _ _ _ _ _ mk sat₁,
    exact sat.not_factory.sat_mk_not mk sat₁ }
end

@[priority 100] -- see Note [lower instance priority]
instance : smt.not_factory (Σ n, vector β n) γ :=
{ mk_not    := λ ⟨n, v⟩, (λ x, sigma.mk n x) <$> (mk_not v),
  le_mk_not := by {
    intros,
    cases e₁,
    apply increasing_map,
    apply le_mk_not },
  sat_mk_not := by {
    intros _ _ _ _ _ _ mk sat₁,
    cases e₁ with n₁ e₁,
    cases e₂ with n₂ e₂,
    simp only [smt.not_factory._match_1, state_t.run_map] at mk,
    cases mk,
    simp only [factory.sat, sat.iff_eval] at sat₁,
    have c := eval.length_eq sat₁, simp only at c, subst c,
    apply eval_mk_not,
    { simp only [prod.mk.eta] },
    { from sat₁ } } }

end bitblast
end smt
