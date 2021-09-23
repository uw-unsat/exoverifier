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
variables [sat.and_factory β γ] [sat.or_factory β γ] [sat.not_factory β γ]

open factory.monad

/-- Create an `ite` circuit. -/
def mk_ite (c : β) : ∀ {n : ℕ}, vector β n → vector β n → state γ (vector β n) :=
mk_binary_bitwise_op (sat.ite_factory.mk_ite c)

theorem le_mk_ite {c : β} {n : ℕ} {v₁ v₂ : vector β n} {g : γ} :
  g ≤ (((mk_ite c v₁ v₂)).run g).2 :=
begin
  simp only [mk_ite],
  apply le_mk_binary_bitwise_op,
  apply sat.ite_factory.le_mk_ite
end

theorem eval_mk_ite {c : β} {n : ℕ} {g g' : γ} {v₁ v₂ v₃ : vector β n} {c_b : bool} {b₁ b₂ : fin n → bool} :
  (mk_ite c v₁ v₂).run g = (v₃, g') →
  factory.sat g c c_b →
  eval g v₁ b₁ →
  eval g v₂ b₂ →
  eval g' v₃ (bv.ite (λ _, c_b) b₁ b₂) :=
begin
  intros mk eval₁ eval₂ eval₃,
  simp only [bv.ite],
  have h := @eval_mk_binary_bitwise_op _ _ _ _ (λ (x y : bool), cond c_b x y) _ _ _ _ _ _ _ _ _ _ mk eval₂ eval₃,
  { simp only at h,
    rw [cond_fn_ext] at h,
    from h },
  { intros _ _,
    apply sat.ite_factory.le_mk_ite },
  { intros _ _ _ _ _ _ _ _ _ _,
    apply sat.ite_factory.sat_mk_ite; try{assumption},
    apply factory.sat_of_le _ eval₁,
    assumption }
end

@[priority 100] -- see Note [lower instance priority]
instance : smt.ite_factory (Σ (n : ℕ), vector β n) γ :=
{ mk_ite    := λ (c : Σ n, vector β n),
    match c with
    | ⟨1, c_b⟩ := sat.demote_mk_binary_op id (λ n x y, @mk_ite _ _ _ _ _ _ c_b.head n x y)
    | _        := λ _ _, pure $ default _
    end,
  le_mk_ite := by {
    intros c _ _,
    cases c with n c,
    { cases n,
      { intros r, refl },
      cases n,
      { apply sat.increasing_demote_mk_binary_op,
        intros,
        apply le_mk_ite },
      { intros r, refl } } },
  sat_mk_ite := by {
    intros _ _ _ _ _ _ _ _ _ _ mk sat₁ sat₂ sat₃,
    cases e₁ with n₁ e₁,
    cases e₂ with n₂ e₂,
    cases e₃ with n₃ e₃,
    cases e₄ with n₄ e₄,
    have c := eval.length_eq sat₁, simp only at c, subst c,
    have c := eval.length_eq sat₂, simp only at c, subst c,
    have c := eval.length_eq sat₃, simp only at c, subst c,
    simp only [factory.sat, sat],
    simp only [smt.ite_factory._match_1, sat.demote_mk_binary_op] at mk,
    split_ifs at mk; try{contradiction},
    simp only [state_t.run_bind] at mk,
    cases mk,
    apply eval_mk_ite,
    by rw [prod.mk.eta],
    { simp only [factory.sat, sat] at sat₁,
      rw [eval.iff_head_tail] at sat₁,
      from sat₁.1 },
    from sat₂,
    from sat₃ } }

end bitblast
end smt
