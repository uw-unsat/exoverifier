/-
Copyright (c) 2021 The UNSAT Group. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luke Nelson, Xi Wang
-/
import .basic
import data.bv.order

universe u
variables {β γ : Type u} [sat.factory β γ]

namespace smt
namespace bitblast
variables [sat.and_factory β γ] [sat.or_factory β γ]
          [sat.implies_factory β γ] [sat.nimplies_factory β γ]

open factory.monad

/-- Helper for `mk_ult`, chaining 1-bit `ult` comparators similarly to ripple-carry adders. -/
def mk_ult_aux : ∀ {n : ℕ}, vector β n → vector β n → β → state γ β
| 0       _  _  c := pure c
| (n + 1) v₁ v₂ c := do
  t ← sat.ult_factory.mk_ult v₁.head v₂.head c,
  @mk_ult_aux n v₁.tail v₂.tail t

lemma le_mk_ult_aux : ∀ {n : ℕ} {v₁ v₂ : vector β n} {c : β} {g : γ},
  g ≤ ((mk_ult_aux v₁ v₂ c).run g).2
| 0       _ _ _ _ := by refl
| (n + 1) _ _ _ _ := by {
  simp only [mk_ult_aux, state_t.run_bind],
  apply le_trans sat.ult_factory.le_mk_ult le_mk_ult_aux }

lemma eval_mk_ult_aux : ∀ {n : ℕ} {g g' : γ} {v₁ v₂ : vector β n} {c r : β} {b₁ b₂ : fin n → bool} {b₃ : bool},
  (mk_ult_aux v₁ v₂ c).run g = (r, g') →
  eval g v₁ b₁ →
  eval g v₂ b₂ →
  factory.sat g c b₃ →
  factory.sat g' r (to_bool ((b₁ < b₂) ∨ ((b₁ = b₂) ∧ b₃)))
| 0       g g' v₁ v₂ c r b₁ b₂ b₃ := λ mk eval₁ eval₂ eval₃, by {
  simp only [mk_ult_aux, state_t.run_pure] at mk,
  cases mk,
  simpa [bv.ult_zero] }
| (n + 1) g g' v₁ v₂ c r b₁ b₂ b₃ := λ mk eval₁ eval₂ eval₃, by {
  simp only [mk_ult_aux, state_t.run_bind] at mk,
  cases step₁ : (sat.ult_factory.mk_ult v₁.head v₂.head c).run g with t g₁,
  simp only [step₁] at mk,

  have gg₁ : g ≤ g₁,
  { have h : g₁ = (t, g₁).2 := rfl, rw [h, ← step₁],
    apply sat.ult_factory.le_mk_ult },

  simp only [eval.iff_head_tail] at eval₁ eval₂,
  cases eval₁ with eval₁_0 eval₁_n,
  cases eval₂ with eval₂_0 eval₂_n,

  have hsat₃ := sat.ult_factory.sat_mk_ult step₁ eval₁_0 eval₂_0 eval₃,
  have h := eval_mk_ult_aux mk (eval.of_le gg₁ eval₁_n) (eval.of_le gg₁ eval₂_n) hsat₃,
  convert h using 2, clear_except,
  rw [bv.eq_succ, bv.ult_succ],
  cases b₁ 0; cases b₂ 0; simp [bimplies] }

section ult
variable [sat.const_factory β γ]

open sat.const_factory

/-- Create an n-bit `ult` comparator. -/
def mk_ult {n : ℕ} (v₁ v₂ : vector β n) : state γ (vector β 1) := do
r ← (mk_false <$> get) >>= mk_ult_aux v₁ v₂,
pure $ r ::ᵥ vector.nil

lemma le_mk_ult {n : ℕ} {v₁ v₂ : vector β n} {g : γ} :
  g ≤ ((mk_ult v₁ v₂).run g).2 :=
begin
  simp only [mk_ult, state_t.run_bind],
  apply le_mk_ult_aux
end

lemma eval_mk_ult {n : ℕ} {g g' : γ} {v₁ v₂ : vector β n} {v₃ : vector β 1} {b₁ b₂ : fin n → bool} :
  (mk_ult v₁ v₂).run g = (v₃, g') →
  eval g v₁ b₁ →
  eval g v₂ b₂ →
  eval g' v₃ (λ _ : fin 1, to_bool (b₁ < b₂)) :=
begin
  intros mk eval₁ eval₂,
  rw [eval.iff_singleton],
  simp only [mk_ult, state_t.run_bind] at mk,
  cases mk, clear mk,
  convert (eval_mk_ult_aux _ eval₁ eval₂ sat_mk_false),
  { simp },
  { rw [vector.head, prod.mk.eta], refl },
end

section
local attribute [irreducible] mk_ult

@[priority 100] -- see Note [lower instance priority]
instance : smt.ult_factory (Σ (n : ℕ), vector β n) γ :=
{ mk_ult    := sat.demote_mk_binary_op (λ _, 1) (@mk_ult β γ _ _ _ _ _ _),
  le_mk_ult := by {
    apply sat.increasing_demote_mk_binary_op,
    apply le_mk_ult },
  sat_mk_ult := by {
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
    refine eval_mk_ult _ sat₁ sat₂,
    rw prod.mk.eta } }

end
end ult
end bitblast
end smt
