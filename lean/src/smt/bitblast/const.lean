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
variable [sat.const_factory β γ]

open factory.monad
open sat.const_factory

/-- Create an n-bit constant. -/
def mk_const {n : ℕ} (c : lsbvector n) : state γ (vector β n) :=
state_t.mk $ λ g,
  (vector.map (λ b, cond b (mk_true g) (mk_false g)) c, g)

lemma le_mk_const {n : ℕ} {c : lsbvector n} {g : γ} :
  g ≤ ((@mk_const β _ _ _ _ c).run g).2 :=
by simp [mk_const]

lemma eval_mk_const {n : ℕ} {g g' : γ} {c : lsbvector n} {v' : vector β n} :
  (mk_const c).run g = (v', g') →
  eval g' v' c.nth :=
begin
  simp only [mk_const],
  intro mk,
  cases mk, clear mk,
  simp only [eval.iff_nth, vector.nth_map],
  intro i,
  cases c.nth i; simp only [cond],
  { apply sat_mk_false },
  { apply sat_mk_true }
end

@[priority 100] -- see Note [lower instance priority]
instance : smt.const_factory (Σ (n : ℕ), vector β n) γ :=
{ mk_const    := λ n c, sigma.mk n <$> mk_const c,
  le_mk_const := λ _ _, by {
    apply increasing_map,
    apply le_mk_const },
  sat_mk_const := by {
    intros _ _ _ _ _ mk,
    cases mk, clear mk,
    simp only [factory.sat, sat],
    apply eval_mk_const,
    simp only [mk_const] } }

end bitblast
end smt
