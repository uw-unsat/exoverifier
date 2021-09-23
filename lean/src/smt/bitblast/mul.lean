/-
Copyright (c) 2021 The UNSAT Group. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luke Nelson, Xi Wang
-/
import .const
import .add
import .ite
import data.bv.mul

universe u
variables {β γ : Type u} [sat.factory β γ]

namespace smt
namespace bitblast
variables [sat.const_factory β γ] [sat.and_factory β γ] [sat.or_factory β γ] [sat.xor_factory β γ]

open factory.monad
open sat.and_factory

/-- Create a multiplier. -/
def mk_mul : ∀ {n : ℕ} (v₁ v₂ : vector β n), state γ (vector β n)
| 0       _  _  := pure vector.nil
| (n + 1) v₁ v₂ := do
  p ← mk_unary_bitwise_op (mk_and v₂.head) v₁,
  r ← @mk_mul n v₁.init v₂.tail,
  s ← mk_add p.tail r,
  pure $ p.head ::ᵥ s.1

lemma le_mk_mul : ∀ {n : ℕ} {v₁ v₂ : vector β n} {g : γ},
  g ≤ ((mk_mul v₁ v₂).run g).2
| 0       _ _ _ := by refl
| (n + 1) _ _ _ := by {
  simp only [mk_mul, state_t.run_bind, state_t.run_pure],
  apply le_trans _ le_mk_add,
  apply le_trans _ le_mk_mul,
  apply le_mk_unary_bitwise_op,
  apply le_mk_and }

lemma eval_mk_mul : ∀ {n : ℕ} {g g' : γ} {v₁ v₂ v₃ : vector β n} {b₁ b₂ : fin n → bool},
  (mk_mul v₁ v₂).run g = (v₃, g') →
  eval g v₁ b₁ →
  eval g v₂ b₂ →
  eval g' v₃ (b₁ * b₂)
| 0       g g' v₁ v₂ v₃ b₁ b₂ := by {
  intros,
  rw [vector.eq_nil v₃],
  constructor }
| (n + 1) g g' v₁ v₂ v₃ b₁ b₂ := by {
  intros mk eval₁ eval₂,
  rw [eval.iff_head_tail] at eval₂ ⊢,
  cases eval₂ with eval₂_0 eval₂_n,

  simp only [mk_mul] at mk,
  simp only [state_t.run_bind, state_t.run_pure] at mk,
  simp only [has_bind.bind, id_bind, pure, id] at mk,

  cases step₁ : (mk_unary_bitwise_op (mk_and v₂.head) v₁).run g with p g₁,
  cases step₂ : (mk_mul v₁.init v₂.tail).run g₁ with r g₂,
  cases step₃ : (mk_add p.tail r).run g₂ with s g₃,
  simp only [step₁, step₂, step₃] at mk,

  cases mk, clear mk,
  simp only [vector.cons_head, vector.cons_tail],

  have gg₁ : g ≤ g₁,
  { have h : g₁ = (p, g₁).2 := rfl, rw [h, ← step₁],
    apply le_mk_unary_bitwise_op, apply le_mk_and },
  have g₁g₂ : g₁ ≤ g₂,
  { have h : g₂ = (r, g₂).2 := rfl, rw [h, ← step₂],
    apply le_mk_mul },
  have g₂g' : g₂ ≤ g',
  { have h : g' = (s, g').2 := rfl, rw [h, ← step₃],
    apply le_mk_add },

  have hp : eval g₁ p (λ i, b₂ 0 && b₁ i),
  { apply @eval_mk_unary_bitwise_op _ _ _ _ (λ x, b₂ 0 && x) (@le_mk_and _ _ _ _ v₂.head);
    try { assumption },
    intros _ _ _ _ _ _ _ _, apply sat_mk_and,
    { assumption },
    { apply factory.sat_of_le; assumption },
    { assumption } },
  simp only [bool.band_comm] at hp,

  split,
  { apply factory.sat_of_le (le_trans g₁g₂ g₂g'),
    have h := eval.to_head hp,
    rwa [bv.mul_head] },
  { have hr := eval_mk_mul step₂ (eval.of_le gg₁ (eval.iff_init_last.1 eval₁).1) (eval.of_le gg₁ eval₂_n),
    cases s,
    have hs := (eval_mk_add step₃ (eval.of_le g₁g₂ (eval.iff_head_tail.1 hp).2) hr).1,
    rwa [bv.mul_tail] } }

@[priority 100] -- see Note [lower instance priority]
instance : smt.mul_factory (Σ (n : ℕ), vector β n) γ :=
{ mk_mul    := sat.demote_mk_binary_op id (@mk_mul _ _ _ _ _ _ _),
  le_mk_mul := by {
    apply sat.increasing_demote_mk_binary_op,
    apply le_mk_mul },
  sat_mk_mul := by {
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
    refine eval_mk_mul _ sat₁ sat₂,
    rw prod.mk.eta } }

end bitblast
end smt
