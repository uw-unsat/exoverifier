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
variable [sat.and_factory β γ]

open factory.monad

/-- Create an n-bit AND circuit. -/
def mk_and : ∀ {n : ℕ}, vector β n → vector β n → state γ (vector β n) :=
mk_binary_bitwise_op sat.and_factory.mk_and

theorem le_mk_and {n : ℕ} {v₁ v₂ : vector β n} {g : γ} :
  g ≤ ((mk_and v₁ v₂).run g).2 :=
begin
  simp only [mk_and],
  apply le_mk_binary_bitwise_op,
  apply sat.and_factory.le_mk_and
end

theorem eval_mk_and {n : ℕ} {g g' : γ} {v₁ v₂ v₃ : vector β n} {b₁ b₂ : fin n → bool} :
  (mk_and v₁ v₂).run g = (v₃, g') →
  eval g v₁ b₁ →
  eval g v₂ b₂ →
  eval g' v₃ (bv.and b₁ b₂) :=
begin
  intros mk eval₁ eval₂,
  refine eval_mk_binary_bitwise_op _ _ mk eval₁ eval₂,
  { apply sat.and_factory.le_mk_and },
  { intros _ _ _ _ _ _ _ l mk' sat₁ sat₂,
    exact sat.and_factory.sat_mk_and mk' sat₁ sat₂ }
end

@[priority 100] -- see Note [lower instance priority]
instance : smt.and_factory (Σ (n : ℕ), vector β n) γ :=
{ mk_and    := sat.demote_mk_binary_op id (@mk_and _ _ _ _),
  le_mk_and := by {
    apply sat.increasing_demote_mk_binary_op,
    apply le_mk_and },
  sat_mk_and := by {
    intros _ _ _ _ _ _ _ _ mk sat₁ sat₂,
    cases e₁ with n₁ e₁,
    cases e₂ with n₂ e₂,
    cases e₃ with n₃ e₃,
    have c := eval.length_eq sat₁, simp only at c, subst c,
    have c := eval.length_eq sat₂, simp only at c, subst c,
    simp only [factory.sat, sat],
    simp only [sat.demote_mk_binary_op] at mk,
    split_ifs at mk; try{contradiction},
    simp only [state_t.run_bind] at mk,
    cases mk,
    refine eval_mk_and _ sat₁ sat₂,
    rw prod.mk.eta } }

end bitblast
end smt
