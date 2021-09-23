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
variable [sat.xor_factory β γ]

open factory.monad

/-- Create an n-bit XOR circuit. -/
def mk_xor : ∀ {n : ℕ}, vector β n → vector β n → state γ (vector β n) :=
mk_binary_bitwise_op sat.xor_factory.mk_xor

theorem le_mk_xor {n : ℕ} {v₁ v₂ : vector β n} {g : γ} :
  g ≤ ((mk_xor v₁ v₂).run g).2 :=
begin
  simp only [mk_xor],
  apply le_mk_binary_bitwise_op,
  apply sat.xor_factory.le_mk_xor
end

theorem eval_mk_xor {n : ℕ} {g g' : γ} {v₁ v₂ v₃ : vector β n} {b₁ b₂ : fin n → bool} :
  (mk_xor v₁ v₂).run g = (v₃, g') →
  eval g v₁ b₁ →
  eval g v₂ b₂ →
  eval g' v₃ (bv.xor b₁ b₂) :=
begin
  apply eval_mk_binary_bitwise_op,
  { apply sat.xor_factory.le_mk_xor },
  { intros _ _ _ _ _ _ _ _ mk sat₁ sat₂,
    exact sat.xor_factory.sat_mk_xor mk sat₁ sat₂ }
end

@[priority 100] -- see Note [lower instance priority]
instance : smt.xor_factory (Σ (n : ℕ), vector β n) γ :=
{ mk_xor    := sat.demote_mk_binary_op id (@mk_xor _ _ _ _),
  le_mk_xor := by {
    apply sat.increasing_demote_mk_binary_op,
    apply le_mk_xor },
  sat_mk_xor := by {
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
    refine eval_mk_xor _ sat₁ sat₂,
    rw prod.mk.eta } }

end bitblast
end smt
