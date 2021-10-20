/-
Copyright (c) 2021 The UNSAT Group. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luke Nelson, Xi Wang
-/
import .const
import .ite
import .sub

universe u
variables {β γ : Type u} [sat.factory β γ]

namespace smt
namespace bitblast
variables [sat.const_factory β γ] [sat.not_factory β γ] [sat.and_factory β γ] [sat.or_factory β γ]

/-- Create a divider circuit. -/
def mk_udiv_urem : ∀ {n₁ n₂ : ℕ} (hle : n₁ ≤ n₂),
                     vector β n₁ → vector β n₂ → state γ (vector β n₁ × vector β n₂)
| 0        0        _   _  _  := pure (vector.nil, vector.nil)
| (n₁ + 1) 0        hle _  _  := absurd hle (not_le_of_lt (nat.succ_pos _))
| 0        (n₂ + 1) _   _  _  := do
  r ← mk_const $ vector.of_fn 0,
  pure (vector.nil, r)
| (n₁ + 1) (n₂ + 1) hle v₁ v₂ := do
  qr ← @mk_udiv_urem n₁ (n₂ + 1) (nat.le_of_succ_le hle) v₁.tail v₂,
  r₁ ← pure $ v₁.head ::ᵥ qr.2.init, -- r₁: left-shift the remainder qr.1 with v₁'s lowest bit
  p ← mk_sub r₁ v₂,                  -- p: (r₁ - v₂, r₁ ≥ v₂)
  r ← mk_ite p.2 p.1 r₁,             -- remainder: if r₁ ≥ v₂ then r₁ - v₂ else r₁
  pure (p.2 ::ᵥ qr.1, r)             -- quotient: add r₁ ≥ v₂ as the lowest bit

theorem le_mk_udiv_urem {g : γ} : ∀ {n₁ n₂ : ℕ} {hle : n₁ ≤ n₂}
                                    {v₁ : vector β n₁} {v₂ : vector β n₂},
  g ≤ ((mk_udiv_urem hle v₁ v₂).run g).2
| 0         0       _ _  _  := by refl
| 0        (n₂ + 1) _ _  _  := by {
  apply factory.monad.increasing_pure }
| (n₁ + 1) (n₂ + 1) _ v₁ v₂ := by {
  simp only [mk_udiv_urem, state_t.run_bind, state_t.run_pure],
  apply le_trans _ le_mk_ite,
  apply le_trans _ le_mk_sub,
  apply le_mk_udiv_urem }

private theorem aux_to_nat_cons_eq {n₁ n₂ : ℕ} (hle : n₁ ≤ n₂)
                                   (b₁ : fin (n₁ + 1) → bool) (b₂ : fin (n₂ + 1) → bool) :
  bv.to_nat
    (fin.cons (b₁ 0) (fin.init (bv.of_nat (bv.to_nat (fin.tail b₁) % bv.to_nat b₂)))
     : fin (n₂ + 1) → bool) =
  bv.to_nat b₁ % (2 * bv.to_nat b₂) :=
begin
  simp only [bv.to_nat_cons, bv.to_nat_init, bv.to_of_nat, bv.to_nat_tail],
  simp only [nat.bit_val, nat.div2_val, pow_succ],
  rw [nat.mod_mod_of_dvd _ (dvd_mul_left (2^n₂) 2)],
  rw [← nat.mod_add_div (bv.to_nat b₁ % (2 * bv.to_nat b₂)) 2],
  rw [← nat.div_mod_eq_mod_mul_div],
  rw [nat.mod_mul_right_mod, add_comm],
  congr' 2,
  { rw [bv.to_nat_succ, nat.bit_val],
    simp only [add_comm],
    rw [nat.add_mul_mod_self_left],
    cases b₁ 0; refl },
  { apply nat.mod_eq_of_lt,
    apply lt_of_le_of_lt (nat.mod_le _ _),
    rw [← nat.div2_val, ← bv.to_nat_tail],
    exact lt_of_lt_of_le (bv.to_nat_lt _) (pow_le_pow dec_trivial hle) }
end

private theorem udiv_eq {n₁ n₂ : ℕ} (hle : n₁ ≤ n₂)
                        (b₁ : fin (n₁ + 1) → bool) (b₂ : fin (n₂ + 1) → bool) :
  (fin.cons
    (to_bool (bv.to_nat b₂ ≤ bv.to_nat b₁ % (2 * bv.to_nat b₂)))
    (ite (bv.to_nat b₂ = 0) ⊤ (bv.of_nat (bv.to_nat (fin.tail b₁) / bv.to_nat b₂)))
    : fin (n₁ + 1) → bool) =
  ite (bv.to_nat b₂ = 0) ⊤ (bv.of_nat (bv.to_nat b₁ / bv.to_nat b₂)) :=
begin
  split_ifs with hz,
  { simp only [hz, mul_zero, nat.mod_zero, zero_le, to_bool_true_eq_tt],
    exact fin.cons_self_tail ⊤ },
  { apply bv.eq_of_to_nat_eq_to_nat,
    simp only [bv.to_of_nat, bv.to_nat_cons, bv.to_nat_tail],
    simp only [nat.bit_val, nat.div2_val],
    conv_rhs { rw [nat.mod_pow_succ (show 0 < 2, by dec_trivial),
                   nat.div_div_eq_div_mul, mul_comm _ 2, ← nat.div_div_eq_div_mul] },
    congr' 1,
    rw [mul_comm],
    have hiff : bv.to_nat b₂ ≤ bv.to_nat b₁ % (bv.to_nat b₂ * 2) ↔
                1 ≤ bv.to_nat b₁ / bv.to_nat b₂ % 2,
    { rw [nat.div_mod_eq_mod_mul_div, nat.le_div_iff_mul_le, one_mul],
      omega },
    simp only [hiff],
    by_cases h : 1 ≤ bv.to_nat b₁ / bv.to_nat b₂ % 2;
    simp only [h, to_bool_false_eq_ff, to_bool_true_eq_tt, cond],
    { have := nat.mod_lt (bv.to_nat b₁ / bv.to_nat b₂) (show 0 < 2, by dec_trivial),
      omega },
    { omega } }
end

private theorem urem_eq {n₁ n₂ : ℕ} (hle : n₁ ≤ n₂)
                        (b₁ : fin (n₁ + 1) → bool) (b₂ : fin (n₂ + 1) → bool) :
  (cond
    (to_bool (bv.to_nat b₂ ≤ bv.to_nat b₁ % (2 * bv.to_nat b₂)))
    (fin.cons (b₁ 0)
              (fin.init (bv.of_nat (bv.to_nat (fin.tail b₁) % bv.to_nat b₂))) - b₂
              : fin (n₂ + 1) → bool)
    (fin.cons (b₁ 0)
              (fin.init (bv.of_nat (bv.to_nat (fin.tail b₁) % bv.to_nat b₂))))) =
  (bv.of_nat (bv.to_nat b₁ % bv.to_nat b₂)) :=
begin
  apply bv.eq_of_to_nat_eq_to_nat,
  simp only [bv.to_of_nat],

  have h : bv.to_nat b₁ % bv.to_nat b₂ % 2^(n₂ + 1) = bv.to_nat b₁ % bv.to_nat b₂,
  { apply nat.mod_eq_of_lt,
    by_cases hz : bv.to_nat b₂ = 0,
    { rw [hz, nat.mod_zero],
      apply lt_of_lt_of_le (bv.to_nat_lt _),
      apply pow_le_pow; omega },
    apply lt_trans (nat.mod_lt _ _) (bv.to_nat_lt _),
    omega },
  rw h, clear h,

  by_cases h : bv.to_nat b₂ ≤ bv.to_nat b₁ % (2 * bv.to_nat b₂);
  simp only [h, cond,
             to_bool_true_eq_tt, bool.bnot_true,
             to_bool_false_eq_ff, bool.bnot_false],
  { simp only [bv.sub_to_nat, aux_to_nat_cons_eq hle],
    simp only [h, if_true],
    by_cases hz : bv.to_nat b₂ = 0,
    { simp [hz] },
    have h₁ := nat.sub_mul_mod (bv.to_nat b₁ % (2 * bv.to_nat b₂)) 1 (bv.to_nat b₂),
    simp only [mul_one, nat.mod_mul_left_mod] at h₁, specialize h₁ h,
    rw [← h₁], clear h₁,
    symmetry,
    apply nat.mod_eq_of_lt,
    rw [tsub_lt_iff_right h],
    have h₂ : bv.to_nat b₂ + bv.to_nat b₂ = 2 * bv.to_nat b₂,
    { ring },
    rw h₂, clear h₂,
    apply @nat.mod_lt (bv.to_nat b₁) (2 * bv.to_nat b₂),
    simp [nat.pos_of_ne_zero hz] },
  { simp only [aux_to_nat_cons_eq hle],
    rw [← nat.mod_mod_of_dvd _ (dvd_mul_left (bv.to_nat b₂) 2)],
    symmetry,
    apply nat.mod_eq_of_lt (lt_of_not_ge h) }
end

theorem eval_mk_udiv_urem : ∀ {n₁ n₂ : ℕ} (hle : n₁ ≤ n₂) {g g' : γ}
                              {v₁ : vector β n₁} {v₂ : vector β n₂}
                              {v₃ : vector β n₁} {v₄ : vector β n₂}
                              {b₁ : fin n₁ → bool} {b₂ : fin n₂ → bool},
  (mk_udiv_urem hle v₁ v₂).run g = ((v₃, v₄), g') →
  eval g  v₁ b₁ →
  eval g  v₂ b₂ →
  eval g' v₃ (if bv.to_nat b₂ = 0 then ⊤ else @bv.of_nat n₁ (bv.to_nat b₁ / bv.to_nat b₂)) ∧
  eval g' v₄ (@bv.of_nat n₂ (bv.to_nat b₁ % bv.to_nat b₂))
| 0         0        _   _ _  _  _  _  _  _  _  := λ mk eval₁ eval₂, by {
  simp only [mk_udiv_urem, state_t.run_bind, state_t.run_pure] at mk,
  simp only [pure, id, prod.mk.inj_iff] at mk,
  rcases mk with ⟨⟨_, _⟩, mk⟩,
  simp only [← mk],
  split,
  { convert eval₁; apply subsingleton.elim },
  { convert eval₂; apply subsingleton.elim } }
| 0        (n₂ + 1) hle g g' v₁ v₂ v₃ v₄ b₁ b₂ := λ mk eval₁ eval₂, by {
  simp only [mk_udiv_urem, state_t.run_bind, state_t.run_pure] at mk,

  cases step₁ : (@mk_const β _ _ _ _ (vector.of_fn (0 : fin (n₂ + 1) → bool))).run g with r g₁,
  simp only [step₁] at mk,
  cases mk, clear mk,

  have gg' : g ≤ g',
  { have h : g' = (v₄, g').2 := rfl, rw [h, ← step₁],
    apply le_mk_const },

  split,
  { convert eval.of_le gg' eval₁; apply subsingleton.elim },
  { convert eval_mk_const step₁,
    simp only [nat.zero_mod, bv.to_nat_zero],
    rw [vector.nth_of_fn_ext],
    apply bv.eq_of_to_nat_eq_to_nat,
    simp [bv.zero_to_nat, bv.to_of_nat] } }
| (n₁ + 1) (n₂ + 1) hle g g' v₁ v₂ v₃ v₄ b₁ b₂ := λ mk eval₁ eval₂, by {
  simp only [mk_udiv_urem, state_t.run_bind, state_t.run_pure] at mk,
  simp only [has_bind.bind, id_bind, pure, id] at mk,

  cases step₁ : (mk_udiv_urem (nat.le_of_succ_le hle) v₁.tail v₂).run g with qr g₁,
  cases qr with q' r',
  let r₁ := v₁.head ::ᵥ r'.init,
  cases step₂ : (mk_sub r₁ v₂).run g₁ with p g₂,
  cases p with r₂ cmp,
  cases step₃ : (mk_ite cmp r₂ r₁).run g₂ with r g₃,
  simp only [step₁, step₂, step₃] at mk,
  cases mk, clear mk,

  have gg₁ : g ≤ g₁,
  { have h : g₁ = ((q', r'), g₁).2 := rfl, rw [h, ← step₁],
    apply le_mk_udiv_urem },
  have g₁g₂ : g₁ ≤ g₂,
  { have h : g₂ = ((r₂, cmp), g₂).2 := rfl, rw [h, ← step₂],
    apply le_mk_sub },
  have g₂g' : g₂ ≤ g',
  { have h : g' = (v₄, g').2 := rfl, rw [h, ← step₃],
    apply le_mk_ite },
  have g₁g' := le_trans g₁g₂ g₂g',

  have hqr := eval_mk_udiv_urem (nat.le_of_succ_le hle) step₁ (eval.to_tail eval₁) eval₂,
  have hr₁ := eval.cons_iff.2 ⟨eval.to_head (eval.of_le gg₁ eval₁), eval.to_init hqr.2⟩,
  have hp := eval_mk_sub step₂ hr₁ (eval.of_le gg₁ eval₂),
  simp only [add_le_add_iff_right] at hle,
  simp only [aux_to_nat_cons_eq hle, ge_iff_le] at hp,

  split,
  { have hq := eval.cons_iff.2 ⟨factory.sat_of_le g₂g' hp.2, eval.of_le g₁g' hqr.1⟩,
    rw [← udiv_eq hle],
    convert hq },
  { have hr := eval_mk_ite step₃ hp.2 hp.1 (eval.of_le g₁g₂ hr₁),
    simp only [bv.ite] at hr,
    rw [← urem_eq hle],
    convert hr } }

section udiv

/-- Create an unsigned division circuit. -/
def mk_udiv {n : ℕ} (v₁ v₂ : vector β n) : state γ (vector β n) :=
prod.fst <$> (mk_udiv_urem (le_refl _) v₁ v₂)

theorem le_mk_udiv {n : ℕ} {v₁ v₂ : vector β n} {g : γ} :
  g ≤ ((mk_udiv v₁ v₂).run g).2 :=
begin
  simp only [mk_udiv, state_t.run_map],
  apply le_mk_udiv_urem
end

theorem eval_mk_udiv {n : ℕ} {g g' : γ} {v₁ v₂ v₃ : vector β n} {b₁ b₂ : fin n → bool} :
  (mk_udiv v₁ v₂).run g = (v₃, g') →
  eval g  v₁ b₁ →
  eval g  v₂ b₂ →
  eval g' v₃ (b₁ / b₂) :=
begin
  intros mk eval₁ eval₂,
  simp only [mk_udiv, state_t.run_map] at mk,
  cases mk,
  cases step₁ : (mk_udiv_urem (le_refl _) v₁ v₂).run g with qr _,
  cases qr,
  exact (eval_mk_udiv_urem (le_refl _) step₁ eval₁ eval₂).1
end

@[priority 10] -- see Note [lower instance priority]
instance : smt.udiv_factory (Σ (n : ℕ), vector β n) γ :=
{ mk_udiv    := sat.demote_mk_binary_op id (@mk_udiv _ _ _ _ _ _ _),
  le_mk_udiv := by {
    apply sat.increasing_demote_mk_binary_op,
    apply le_mk_udiv },
  sat_mk_udiv := by {
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
    refine eval_mk_udiv _ sat₁ sat₂,
    rw prod.mk.eta } }

end udiv

section urem

/-- Create an unsigned remainder circuit. -/
def mk_urem {n : ℕ} (v₁ v₂ : vector β n) : state γ (vector β n) :=
prod.snd <$> (mk_udiv_urem (le_refl _) v₁ v₂)

theorem le_mk_urem {n : ℕ} {v₁ v₂ : vector β n} {g : γ} :
  g ≤ ((mk_urem v₁ v₂).run g).2 :=
begin
  simp only [mk_urem, state_t.run_map],
  apply le_mk_udiv_urem
end

theorem eval_mk_urem {n : ℕ} {g g' : γ} {v₁ v₂ v₃ : vector β n} {b₁ b₂ : fin n → bool} :
  (mk_urem v₁ v₂).run g = (v₃, g') →
  eval g  v₁ b₁ →
  eval g  v₂ b₂ →
  eval g' v₃ (b₁ % b₂) :=
begin
  intros mk eval₁ eval₂,
  simp only [mk_urem, state_t.run_map] at mk,
  cases mk,
  cases step₁ : (mk_udiv_urem (le_refl _) v₁ v₂).run g with qr _,
  cases qr,
  exact (eval_mk_udiv_urem (le_refl _) step₁ eval₁ eval₂).2
end

@[priority 10] -- see Note [lower instance priority]
instance : smt.urem_factory (Σ (n : ℕ), vector β n) γ :=
{ mk_urem    := sat.demote_mk_binary_op id (@mk_urem _ _ _ _ _ _ _),
  le_mk_urem := by {
    apply sat.increasing_demote_mk_binary_op,
    apply le_mk_urem },
  sat_mk_urem := by {
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
    refine eval_mk_urem _ sat₁ sat₂,
    rw prod.mk.eta } }

end urem

end bitblast
end smt
