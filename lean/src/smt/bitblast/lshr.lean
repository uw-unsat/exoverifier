/-
Copyright (c) 2021 The UNSAT Group. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luke Nelson, Xi Wang
-/
import .const
import .ite

universe u
variables {β γ : Type u} [sat.factory β γ]

namespace smt
namespace bitblast
variables [sat.const_factory β γ] [sat.not_factory β γ] [sat.and_factory β γ] [sat.or_factory β γ]

open factory.monad

/-- Create an n-bit logical right shift circuit, assuming the shifting amount is reversed. -/
def mk_lshr_rev {n₁ : ℕ} : ∀ {n₂ : ℕ}, vector β n₁ → vector β n₂ → state γ (vector β n₁)
| 0        v₁ _  := pure v₁
| (n₂ + 1) v₁ v₂ := let amount : ℕ := nat.shiftl 1 n₂ in do
  c ← mk_const (vector.of_fn (0 : fin (min n₁ amount) → bool)),
  t ← mk_ite v₂.head (@eq.rec_on _ _ _ _ (by simp) ((v₁.drop amount).append c)) v₁,
  @mk_lshr_rev n₂ t v₂.tail

theorem le_mk_lshr_rev {n₁ : ℕ} : ∀ {n₂ : ℕ} {v₁ : vector β n₁} {v₂ : vector β n₂} {g : γ},
  g ≤ ((mk_lshr_rev v₁ v₂).run g).2
| 0        _  _  _ := by refl
| (n₂ + 1) v₁ v₂ g := by {
  simp only [mk_lshr_rev, state_t.run_bind],
  apply le_trans _ le_mk_lshr_rev,
  apply le_trans le_mk_const le_mk_ite }

private theorem cast_ite (n₁ n₂ : ℕ) :
  min n₁ (nat.shiftl 1 n₂) + (n₁ - nat.shiftl 1 n₂) = n₁ :=
by simp [add_comm]

private theorem lshr_reverse_eq {n₁ n₂ : ℕ} (b₁ : fin n₁ → bool) (b₂ : fin (n₂ + 1) → bool) :
  bv.lshr b₁ (fin.reverse b₂) =
  bv.lshr (cond (b₂ 0) (eq.rec (bv.concat 0 (bv.drop _ b₁)) (cast_ite n₁ n₂)) b₁)
          (fin.reverse (fin.tail b₂)) :=
begin
  rw [fin.reverse_tail_eq_init_reverse, ← fin.reverse_last_eq_head b₂],
  generalize : fin.reverse b₂ = b₂',
  conv_lhs { rw [← fin.snoc_init_self b₂'] },
  simp only [bv.lshr, bv.to_of_nat, bv.to_nat_snoc],
  cases (b₂' (fin.last n₂));
  simp only [cond],
  { simp },
  { simp only [fin.cast_eq_rec @bv.to_nat, mul_one],
    rw [pow_add, nat.one_shiftl],
    rw [bv.to_nat_concat, bv.zero_to_nat, mul_zero, add_zero],
    rw [bv.to_nat_drop],
    rw [mul_comm, nat.div_div_eq_div_mul] }
end

theorem eval_mk_lshr_rev {n₁ : ℕ} : ∀ {n₂ : ℕ} {g g' : γ} {v₁ : vector β n₁} {v₂ : vector β n₂}
                                      {v₃ : vector β n₁} {b₁ : fin n₁ → bool} {b₂ : fin n₂ → bool},
  (mk_lshr_rev v₁ v₂).run g = (v₃, g') →
  eval g v₁ b₁ →
  eval g v₂ b₂ →
  eval g' v₃ (bv.lshr b₁ (fin.reverse b₂))
| 0        g g' v₁ v₂ v₃ b₁ b₂ := λ mk eval₁ eval₂, by {
  suffices : eval g' v₃ b₁, by simpa [bv.lshr],
  cases mk, exact eval₁ }
| (n₂ + 1) g g' v₁ v₂ v₃ b₁ b₂ := λ mk eval₁ eval₂, by {
  rw [eval.iff_head_tail] at eval₂,
  cases eval₂ with eval₂_0 eval₂_n,

  simp only [mk_lshr_rev] at mk,
  simp only [state_t.run_bind] at mk,
  simp only [has_bind.bind, id_bind] at mk,

  cases step₁ : (@mk_const β _ _ _ _ (vector.of_fn (0 : fin (min n₁ (nat.shiftl 1 n₂)) → bool))).run g with c g₁,
  cases step₂ : (mk_ite v₂.head (@eq.rec_on _ _ _ _ (by simp) ((v₁.drop (nat.shiftl 1 n₂)).append c)) v₁).run g₁ with t g₂,
  cases step₃ : (mk_lshr_rev t v₂.tail).run g₂ with r g₃,
  simp only [step₁, step₂, step₃] at mk,
  cases mk, clear mk,

  have gg₁ : g ≤ g₁,
  { have h : g₁ = (c, g₁).2 := rfl, rw [h, ← step₁],
    apply le_mk_const },

  have g₁g₂ : g₁ ≤ g₂,
  { have h : g₂ = (t, g₂).2 := rfl, rw [h, ← step₂],
    apply le_mk_ite },

  have hc := eval_mk_const step₁,
  rw [vector.nth_of_fn_ext] at hc,

  have ht' := eval.to_append (eval.to_drop (nat.shiftl 1 n₂) (eval.of_le gg₁ eval₁)) hc,
  have ht := eval_mk_ite step₂ (factory.sat_of_le gg₁ eval₂_0)
                         (eval.iff_eq_rec.1 ht') (eval.of_le gg₁ eval₁),
  clear ht', swap, { apply cast_ite },

  have hr := eval_mk_lshr_rev step₃ ht (eval.of_le (le_trans gg₁ g₁g₂) eval₂_n),
  convert hr using 1, clear_except,
  apply lshr_reverse_eq }

/-- Create an n-bit left shift circuit. -/
def mk_lshr {n₁ n₂ : ℕ} (v₁ : vector β n₁) (v₂ : vector β n₂) : state γ (vector β n₁) :=
mk_lshr_rev v₁ v₂.reverse

theorem le_mk_lshr {n₁ n₂ : ℕ} {v₁ : vector β n₁} {v₂ : vector β n₂} {g : γ} :
  g ≤ ((mk_lshr v₁ v₂).run g).2 :=
le_mk_lshr_rev

theorem eval_mk_lshr {n₁ n₂ : ℕ} {g g' : γ} {v₁ : vector β n₁} {v₂ : vector β n₂}
                     {v₃ : vector β n₁} {b₁ : fin n₁ → bool} {b₂ : fin n₂ → bool} :
  (mk_lshr v₁ v₂).run g = (v₃, g') →
  eval g v₁ b₁ →
  eval g v₂ b₂ →
  eval g' v₃ (bv.lshr b₁ b₂) :=
begin
  intros mk eval₁ eval₂,
  rw [← fin.reverse_reverse b₂],
  apply eval_mk_lshr_rev mk eval₁ (eval.iff_reverse.1 eval₂)
end

@[priority 100] -- see Note [lower instance priority]
instance : smt.lshr_factory (Σ (n : ℕ), vector β n) γ :=
{ mk_lshr     := sat.demote_mk_shift_op (@mk_lshr _ _ _ _ _ _ _),
  le_mk_lshr  := by {
    apply sat.increasing_demote_mk_shift_op,
    apply le_mk_lshr },
  sat_mk_lshr := by {
    intros _ _ _ _ _ _ _ _ _ mk sat₁ sat₂,
    cases e₁ with n₁ e₁,
    cases e₂ with n₂ e₂,
    cases e₃ with n₃ e₃,
    have c := eval.length_eq sat₁, simp only at c, subst c,
    have c := eval.length_eq sat₂, simp only at c, subst c,
    simp only [sat.demote_mk_shift_op] at mk,
    simp only [← bind_pure_comp_eq_map] at mk,
    simp only [state_t.run_bind, state_t.run_pure] at mk,
    cases mk, clear mk,
    simp only [factory.sat, sat],
    refine eval_mk_lshr _ sat₁ sat₂,
    rw [prod.mk.eta] } }

end bitblast
end smt
