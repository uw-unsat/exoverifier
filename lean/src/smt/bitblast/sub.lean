/-
Copyright (c) 2021 The UNSAT Group. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luke Nelson, Xi Wang
-/
import .add
import .not
import data.bv.sbc

universe u
variables {β γ : Type u} [sat.factory β γ]

namespace smt
namespace bitblast
variables [sat.not_factory β γ] [sat.and_factory β γ] [sat.or_factory β γ] [sat.xor_factory β γ]

open factory.monad

/-- Create an n-bit subtract with carry. -/
def mk_sbc {n : ℕ} (v₁ v₂ : vector β n) (c : β) : state γ (vector β n × β) := do
n_v₂ ← mk_not v₂,
mk_adc v₁ n_v₂ c

lemma le_mk_sbc {n : ℕ} {v₁ v₂ : vector β n} {c : β} {g : γ} :
  g ≤ ((mk_sbc v₁ v₂ c).run g).2 :=
begin
  simp only [mk_sbc, state_t.run_bind],
  apply le_trans le_mk_not le_mk_adc
end

lemma eval_mk_sbc {n : ℕ} {g g' : γ} {v₁ v₂ v₃ : vector β n} {c c' : β}
                  {b₁ b₂ : fin n → bool} {c_b : bool} :
  (mk_sbc v₁ v₂ c).run g = ((v₃, c'), g') →
  eval g  v₁ b₁ →
  eval g  v₂ b₂ →
  factory.sat g c c_b →
  eval g' v₃ (bv.sbc b₁ b₂ c_b) ∧ factory.sat g' c' (to_bool (¬ bv.sbc_overflow b₁ b₂ c_b)) :=
begin
  intros mk eval₁ eval₂ sat₁,
  simp only [mk_sbc, state_t.run_bind] at mk,
  simp only [has_bind.bind, id_bind] at mk,
  cases step₁ : (mk_not v₂).run g with n_v₂ g₁,
  cases step₂ : (mk_adc v₁ n_v₂ c).run g₁ with r g₂,
  simp only [step₁, step₂] at mk,
  cases mk, clear mk,

  have gg₁ : g ≤ g₁,
  { have h : g₁ = (n_v₂, g₁).2 := rfl, rw [h, ← step₁],
    apply le_mk_not },

  have hn_v₂ := eval_mk_not step₁ eval₂,
  have hv₃ := eval_mk_adc step₂ (eval.of_le gg₁ eval₁) hn_v₂ (factory.sat_of_le gg₁ sat₁),
  split,
  { convert hv₃.1 using 1,
    rw [bv.sbc_eq_adc] },
  { convert hv₃.2 using 2,
    rw [bv.sbc_overflow_iff_not_adc_overflow, not_not] }
end

section sub
variable [sat.const_factory β γ]

open sat.const_factory

/-- Create an n-bit subtraction circuit. -/
def mk_sub {n : ℕ} (v₁ v₂ : vector β n) : state γ (vector β n × β) :=
(mk_true <$> get) >>= mk_sbc v₁ v₂

lemma le_mk_sub {n : ℕ} {v₁ v₂ : vector β n} {g : γ} :
  g ≤ ((mk_sub v₁ v₂).run g).2 :=
le_mk_sbc

lemma eval_mk_sub {n : ℕ} {g g' : γ} {v₁ v₂ v₃ : vector β n} {c' : β} {b₁ b₂ : fin n → bool} :
  (mk_sub v₁ v₂).run g = ((v₃, c'), g') →
  eval g  v₁ b₁ →
  eval g  v₂ b₂ →
  eval g' v₃ (b₁ - b₂) ∧ factory.sat g' c' (to_bool (bv.to_nat b₁ ≥ bv.to_nat b₂)) :=
begin
  intros mk eval₁ eval₂,
  simp only [mk_sub] at mk,
  rw [bv.sub_eq_sbc],
  convert eval_mk_sbc mk eval₁ eval₂ sat_mk_true,
  simp [bv.sbc_overflow]
end

section
local attribute [irreducible] mk_sub

@[priority 100] -- see Note [lower instance priority]
instance : smt.sub_factory (Σ n, vector β n) γ :=
{ mk_sub    := sat.demote_mk_binary_op id (λ {_} v₁ v₂, prod.fst <$> mk_sub v₁ v₂),
  le_mk_sub := by {
    apply sat.increasing_demote_mk_binary_op,
    intros, apply increasing_map,
    apply le_mk_sub },
  sat_mk_sub := by {
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
    cases step₁ : (mk_sub e₁ e₂).run g with r _,
    cases r,
    exact (eval_mk_sub step₁ sat₁ sat₂).1 } }

end -- section
end sub
end bitblast
end smt
