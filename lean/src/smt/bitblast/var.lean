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
variable [sat.var_factory β γ]

open factory.monad

/-- Create an n-bit variable. -/
def mk_var : ∀ {n : ℕ}, erased (fin n → bool) → state γ (vector β n)
| 0       := λ _, pure vector.nil
| (n + 1) := λ f, do
  t ← sat.var_factory.mk_var $ f.bind (λ f', erased.mk $ f' 0),
  r ← @mk_var n $ f.bind (λ f', erased.mk $ fin.tail f'),
  pure $ t ::ᵥ r

lemma le_mk_var : ∀ {n : ℕ} {v : erased (fin n → bool)} {g : γ},
  g ≤ ((mk_var v : state γ (vector β n)).run g).2
| 0       _ _ := by refl
| (n + 1) _ _ := by {
  simp only [mk_var, state_t.run_bind],
  apply le_trans sat.var_factory.le_mk_var le_mk_var }

lemma eval_mk_var : ∀ {n : ℕ} {g g' : γ} (v : erased (fin n → bool)) (b : vector β n),
  (mk_var v).run g = (b, g') →
  eval g' b v.out
| 0       g g' v b h := by {
  rw [vector.eq_nil b],
  constructor }
| (n + 1) g g' v b h := by {
  simp only [mk_var, state_t.run_bind, state_t.run_pure] at h,
  simp only [has_bind.bind, id_bind, pure] at h,
  cases h,
  clear h,
  apply eval.of_tail,
  { simp only [vector.cons_head],
    refine factory.sat_of_le (by apply le_mk_var) _,
    rw [← erased.out_mk (v.out 0)],
    apply sat.var_factory.sat_mk_var,
    simp only [erased.out_mk, erased.bind_eq_out, prod.mk.eta] },
  { rw [← erased.out_mk (fin.tail v.out)],
    apply eval_mk_var,
    simp only [erased.out_mk, erased.bind_eq_out, prod.mk.eta, vector.cons_tail] } }

@[priority 100] -- see Note [lower instance priority]
instance : smt.var_factory (Σ n, vector β n) γ :=
{ mk_var := λ {n} (v : erased (fin n → bool)), (λ x, sigma.mk n x) <$> (mk_var v),
  le_mk_var := by {
    intros,
    apply increasing_map,
    apply le_mk_var },
  sat_mk_var := by {
    intros _ _ _ _ _ mk,
    simp only [state_t.run_map] at mk,
    cases mk,
    apply eval_mk_var,
    simp only [prod.mk.eta] } }

end bitblast
end smt
