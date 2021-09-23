/-
Copyright (c) 2021 The UNSAT Group. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luke Nelson, Xi Wang
-/
import .basic
import data.bv.adc

universe u
variables {β γ : Type u} [sat.factory β γ]

namespace smt
namespace bitblast
variables [sat.and_factory β γ] [sat.or_factory β γ] [sat.xor_factory β γ]

open factory.monad
open sat.full_add_factory

/-- Create an adder with carry. -/
def mk_adc : ∀ {n : ℕ}, vector β n → vector β n → β → state γ (vector β n × β)
| 0       _  _  c := pure (vector.nil, c)
| (n + 1) v₁ v₂ c := do
  t ← mk_full_add v₁.head v₂.head c,
  r ← @mk_adc n v₁.tail v₂.tail t.2,
  pure (t.1 ::ᵥ r.1, r.2)

lemma le_mk_adc : ∀ {n : ℕ} {v₁ v₂ : vector β n} {c : β} {g : γ},
  g ≤ ((mk_adc v₁ v₂ c).run g).2
| 0       _ _ _ _ := by refl
| (n + 1) _ _ _ _ := by {
  simp only [mk_adc, state_t.run_bind, state_t.run_pure],
  apply le_trans le_mk_full_add le_mk_adc }

lemma eval_mk_adc : ∀ {n : ℕ} {g g' : γ} {v₁ v₂ v₃ : vector β n} {c c' : β}
                      {b₁ b₂ : fin n → bool} {c_b : bool},
  (mk_adc v₁ v₂ c).run g = ((v₃, c'), g') →
  eval g v₁ b₁ →
  eval g v₂ b₂ →
  factory.sat g c c_b →
  eval g' v₃ (bv.adc b₁ b₂ c_b) ∧ factory.sat g' c' (to_bool (bv.adc_overflow b₁ b₂ c_b))
| 0       g g' v₁ v₂ v₃ c c' b₁ b₂ c_b := λ mk eval₁ eval₂ sat₁, by {
  simp only [mk_adc, state_t.run_bind, state_t.run_pure] at mk,
  cases mk, clear mk,
  split,
  { constructor },
  { cases c_b; simpa [bv.adc_overflow] } }
| (n + 1) g g' v₁ v₂ v₃ c c' b₁ b₂ c_b := λ mk eval₁ eval₂ sat₁, by {
  rw [eval.iff_head_tail] at ⊢ eval₁ eval₂,
  cases eval₁ with eval₁_0 eval₁_n,
  cases eval₂ with eval₂_0 eval₂_n,
  simp only [mk_adc, state_t.run_bind, state_t.run_pure] at mk,
  simp only [has_bind.bind, id_bind, pure, id] at mk,

  cases step₁ : (mk_full_add v₁.head v₂.head c).run g with t g₁,
  cases t with t_sum t_cout,
  cases step₂ : (mk_adc v₁.tail v₂.tail t_cout).run g₁ with r g₂,
  cases r with r_sum r_cout,
  simp only [step₁, step₂] at mk,
  cases mk, clear mk,

  have gg₁ : g ≤ g₁,
  { have h : g₁ = ((t_sum, t_cout), g₁).2 := rfl, rw [h, ← step₁],
    apply le_mk_full_add },
  have g₁g' : g₁ ≤ g',
  { have h : g' = ((r_sum, c'), g').2 := rfl, rw [h, ← step₂],
    apply le_mk_adc },

  have hsum := sat_mk_full_add_sum step₁ eval₁_0 eval₂_0 sat₁,
  have hcout := sat_mk_full_add_carry step₁ eval₁_0 eval₂_0 sat₁,
  have hr := eval_mk_adc step₂ (eval.of_le gg₁ eval₁_n) (eval.of_le gg₁ eval₂_n) hcout,
  cases hr with hr_sum hr_cout,

  split,
  { simp only [vector.cons_head, vector.cons_tail],
    split,
    { rw [bv.adc_zero],
      exact factory.sat_of_le g₁g' hsum },
    { simp only [fin.tail, bv.adc_succ],
      exact hr_sum } },
  { convert hr_cout using 2,
    rw [bv.adc_overflow_succ] } }

section add
variable [sat.const_factory β γ]

open sat.const_factory

/-- Create an adder. -/
def mk_add {n : ℕ} (v₁ v₂ : vector β n) : state γ (vector β n × β) :=
state_t.mk $ λ g,
  (mk_adc v₁ v₂ (mk_false g)).run g

lemma le_mk_add {n : ℕ} {v₁ v₂ : vector β n} {g : γ} :
  g ≤ ((mk_add v₁ v₂).run g).2 :=
le_mk_adc

lemma eval_mk_add {n : ℕ} {g g' : γ} {v₁ v₂ v₃ : vector β n} {c' : β} {b₁ b₂ : fin n → bool} :
  (mk_add v₁ v₂).run g = ((v₃, c'), g') →
  eval g v₁ b₁ →
  eval g v₂ b₂ →
  eval g' v₃ (b₁ + b₂) ∧ factory.sat g' c' (to_bool (bv.adc_overflow b₁ b₂ ff)) :=
begin
  intros mk eval₁ eval₂,
  simp only [mk_add] at mk,
  rw [bv.add_eq_adc],
  exact eval_mk_adc mk eval₁ eval₂ sat_mk_false
end

section
local attribute [irreducible] mk_add

@[priority 100] -- see Note [lower instance priority]
instance : smt.add_factory (Σ (n : ℕ), vector β n) γ :=
{ mk_add    := sat.demote_mk_binary_op id (λ {_} v₁ v₂, prod.fst <$> mk_add v₁ v₂),
  le_mk_add := by {
    apply sat.increasing_demote_mk_binary_op,
    intros, apply increasing_map,
    apply le_mk_add },
  sat_mk_add := by {
    intros _ _ _ _ _ _ _ _ mk sat₁ sat₂,
    cases e₁ with n₁ e₁,
    cases e₂ with n₂ e₂,
    cases e₃ with n₃ e₃,
    have c := eval.length_eq sat₁, simp only at c, subst c,
    have c := eval.length_eq sat₂, simp only at c, subst c,
    simp only [factory.sat, sat],
    simp only [sat.demote_mk_binary_op] at mk,
    split_ifs at mk; try{contradiction},
    simp only [state_t.run_bind, state_t.run_map] at mk,
    cases mk,
    cases step₁ : (mk_add e₁ e₂).run g with r _,
    cases r,
    exact (eval_mk_add step₁ sat₁ sat₂).1 } }

end -- section
end add
end bitblast
end smt
