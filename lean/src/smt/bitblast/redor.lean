/-
Copyright (c) 2021 The UNSAT Group. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luke Nelson, Xi Wang
-/
import .basic
import data.bv.all

universe u
variables {β γ : Type u} [sat.factory β γ]

namespace smt
namespace bitblast
variable [sat.any_factory β γ]

open factory.monad

/-- Create a redor-testing circuit. -/
def mk_redor {n : ℕ} (v : vector β n) : state γ (vector β 1) := do
r ← sat.any_factory.mk_any v.to_list,
pure $ r ::ᵥ vector.nil

theorem le_mk_redor {n : ℕ} {v : vector β n} {g : γ} :
  g ≤ ((mk_redor v).run g).2 :=
begin
  simp only [mk_redor],
  apply increasing_bind,
  { apply sat.any_factory.le_mk_any },
  { simp }
end

theorem eval_mk_redor {n : ℕ} {g g' : γ} (v₁ : vector β n) (v₂ : vector β 1) (b₁ : fin n → bool) :
  (mk_redor v₁).run g = (v₂, g') →
  eval g v₁ b₁ →
  eval g' v₂ (λ _ : fin 1, bv.any b₁) :=
begin
  intros mk eval₁,
  simp only [mk_redor, state_t.run_bind, state_t.run_pure] at mk,
  simp only [has_bind.bind, id_bind, pure, id] at mk,
  simp only [prod.mk.inj_iff] at mk,
  rw [vector.cons_nil_eq_iff_eq_head, ← prod.mk.inj_iff, prod.mk.eta] at mk,
  have h := sat.any_factory.sat_mk_any mk _,
  { rw [eval.iff_singleton],
    apply h },
  { rw [← eval.iff_forall₂],
    from eval₁ }
end

@[priority 100] -- see Note [lower instance priority]
instance : smt.redor_factory (Σ n, vector β n) γ :=
{ mk_redor    := λ ⟨n, v⟩, (λ x, sigma.mk 1 x) <$> (mk_redor v),
  le_mk_redor := by {
    intros,
    cases e₁,
    apply increasing_map,
    apply le_mk_redor },
  sat_mk_redor := by {
    intros _ _ _ _ _ _ mk sat₁,
    cases e₁ with n₁ e₁,
    cases e₂ with n₂ e₂,
    simp only [smt.redor_factory._match_1, state_t.run_map] at mk,
    cases mk,
    simp only [factory.sat, sat.iff_eval] at sat₁,
    have c := eval.length_eq sat₁, simp only at c, subst c,
    apply eval_mk_redor,
    { simp only [prod.mk.eta] },
    { from sat₁ } } }

end bitblast
end smt
