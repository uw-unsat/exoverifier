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
variable [sat.iff_factory β γ]

/-- Create an n-bit IFF circuit. -/
def mk_iff : ∀ {n : ℕ}, vector β n → vector β n → state γ (vector β n) :=
mk_binary_bitwise_op sat.iff_factory.mk_iff

theorem le_mk_iff {n : ℕ} {v₁ v₂ : vector β n} {g : γ} :
  g ≤ ((mk_iff v₁ v₂).run g).2 :=
begin
  simp only [mk_iff],
  apply le_mk_binary_bitwise_op,
  apply sat.iff_factory.le_mk_iff
end

theorem eval_mk_iff {n : ℕ} {g g' : γ} {v₁ v₂ v₃ : vector β n} {b₁ b₂ : fin n → bool} :
  (mk_iff v₁ v₂).run g = (v₃, g') →
  eval g v₁ b₁ →
  eval g v₂ b₂ →
  eval g' v₃ (λ i, biff (b₁ i) (b₂ i)) :=
begin
  intros mk eval₁ eval₂,
  refine eval_mk_binary_bitwise_op _ _ mk eval₁ eval₂,
  { apply sat.iff_factory.le_mk_iff },
  { intros _ _ _ _ _ _ _ l mk' sat₁ sat₂,
    exact sat.iff_factory.sat_mk_iff mk' sat₁ sat₂ }
end

section eq
variables [sat.all_factory β γ]

/-- Create an n-bit equality comparison. -/
def mk_eq {n : ℕ} (v₁ v₂ : vector β n) : state γ (vector β 1) := do
r ← mk_iff v₁ v₂,
l ← sat.all_factory.mk_all r.to_list,
pure (l ::ᵥ vector.nil)

theorem le_mk_eq {n : ℕ} {v₁ v₂ : vector β n} {g : γ} :
  g ≤ ((mk_eq v₁ v₂).run g).2 :=
begin
  simp only [mk_eq, state_t.run_bind],
  transitivity ((mk_iff v₁ v₂).run g).2,
  { apply le_mk_iff },
  { apply sat.all_factory.le_mk_all }
end

theorem eval_mk_eq {n : ℕ} {g g' : γ} {v₁ v₂ : vector β n} {v₃ : vector β 1} {b₁ b₂ : fin n → bool} :
  (mk_eq v₁ v₂).run g = (v₃, g') →
  eval g v₁ b₁ →
  eval g v₂ b₂ →
  eval g' v₃ (λ _ : fin 1, to_bool (b₁ = b₂)) :=
begin
  intros mk eval₁ eval₂,
  simp only [mk_eq, state_t.run_bind, state_t.run_pure] at mk,
  simp only [has_bind.bind, id_bind, pure, id] at mk,
  simp only [prod.mk.inj_iff] at mk,
  rw [vector.cons_nil_eq_iff_eq_head, ← prod.mk.inj_iff, prod.mk.eta] at mk,
  have h := sat.all_factory.sat_mk_all mk _,
  { rw [eval.iff_singleton, ← bv.all_biff_eq_to_bool_eq b₁ b₂],
    apply h },
  { rw [← eval.iff_forall₂],
    exact eval_mk_iff (by rw [prod.mk.eta]) eval₁ eval₂ }
end

@[priority 100] -- see Note [lower instance priority]
instance : smt.eq_factory (Σ (n : ℕ), vector β n) γ :=
{ mk_eq    := sat.demote_mk_binary_op (λ _, 1) (@mk_eq β γ _ _ _),
  le_mk_eq := by {
    apply sat.increasing_demote_mk_binary_op,
    apply le_mk_eq },
  sat_mk_eq := by {
    intros _ _ _ _ _ _ _ _ mk sat₁ sat₂,
    cases e₁ with n₁ e₁,
    cases e₂ with n₂ e₂,
    cases e₃ with n₃ e₃,
    have c := eval.length_eq sat₁, simp only at c, subst c,
    have c := eval.length_eq sat₂, simp only at c, subst c,
    simp only [factory.sat, sat.iff_eval],
    simp only [sat.demote_mk_binary_op] at mk,
    split_ifs at mk; try{contradiction},
    simp only [state_t.run_bind] at mk,
    cases mk,
    refine eval_mk_eq _ sat₁ sat₂,
    rw prod.mk.eta } }

end eq
end bitblast
end smt
