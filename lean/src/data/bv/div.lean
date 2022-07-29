/-
Copyright (c) 2021 The UNSAT Group. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luke Nelson, Xi Wang
-/
import .basic
import data.rat.floor

/-!
# Division by constant

This file provides support for division by constant.

## References

* Torbjörn Granlund and Peter L. Montgomery. *Division by Invariant Integers using Multiplication*.
  <https://gmplib.org/~tege/divcnst-pldi94.pdf>
-/

namespace bv

-- Theorem 4.2: m / 2^(n + l) can be viewed as an approximation of 1 / y.
theorem div_eq_reciprocal_mul_div_of_reciprocal {n l x y m : ℕ} :
  x < 2^n →
  2^(n + l) ≤ m * y →
  m * y ≤ 2^(n + l) + 2^l →
  x / y = m * x / 2^(n + l) :=
begin
  intros hx hmy_lo hmy_hi,

  have hy : y ≠ 0,
  { contrapose! hmy_lo,
    simp only [hmy_lo],
    exact pow_pos dec_trivial _ },
  have hy' : (y : ℚ) ≠ 0,
  { simp [hy] },

  let k : ℤ := m * y - 2^(n + l),
  have hk_lo : 0 ≤ k,
  { simp only [k], linarith },
  have hk_hi : k ≤ 2^l,
  { simp only [k], linarith },

  let q : ℤ := x / y,
  let r : ℤ := x % y,
  have hr_lo : 0 ≤ r,
  { apply int.mod_nonneg,
    rwa [int.coe_nat_ne_zero] },
  have hr_hi : r ≤ y - 1,
  { rw int.le_sub_one_iff,
    apply int.mod_lt_of_pos,
    rw [int.coe_nat_pos],
    apply nat.pos_of_ne_zero hy },
  have hq : (q : ℚ) = (x - r) / y,
  { simp only [q, r, int.mod_def],
    simp [mul_div_cancel_left _ hy'] },

  -- (4.4)
  have hsub : ((m * x : ℤ) : ℚ) / (2^(n + l) : ℕ) - q =
              ((k : ℚ) / 2^l) * ((x : ℚ) / 2^n) * (1 / y) + r / y,
  { have hpow2_n_l : ((2^(n + l) : ℕ) : ℚ) = (2^(n + l) : ℚ), by simp,
    simp only [int.cast_mul, int.cast_coe_nat, hpow2_n_l], clear hpow2_n_l,
    have hm : (m : ℚ) = (k + 2^(n + l)) / y,
    { simp [k, mul_div_cancel _ hy'] },
    rw [hm, hq, sub_div, ← sub_add], clear hm,
    congr' 1,
    conv_rhs { simp only [div_mul_div_comm] },
    rw [div_sub_div _ _ (pow_ne_zero _ (show (2 : ℚ) ≠ 0, by simp)) hy'],
    congr' 1,
    { rw [mul_assoc, mul_comm ↑x ↑y, ← mul_assoc],
      rw [div_mul_cancel _ hy'],
      ring },
    { ring_exp } },

  have hsub_lo : (q : ℚ) ≤ ((m * x : ℤ) : ℚ) / (2^(n + l) : ℕ),
  { rw [← sub_nonneg, hsub], apply add_nonneg,
    { repeat { apply div_nonneg <|> apply mul_nonneg },
      { rwa int.cast_nonneg },
      { exact pow_nonneg dec_trivial _ },
      { apply nat.cast_nonneg },
      { exact pow_nonneg dec_trivial _ },
      { dec_trivial },
      { apply nat.cast_nonneg } },
    { apply div_nonneg,
      { rwa int.cast_nonneg },
      { apply nat.cast_nonneg } } },
  have hsub_hi : ((m * x : ℤ) : ℚ) / (2^(n + l) : ℕ) < (q : ℚ) + 1,
  { rw [← sub_lt_iff_lt_add', hsub],
    have hle₁ : (k : ℚ) / 2^l ≤ 1,
    { rw div_le_one,
      { have h : (2^l : ℚ) = (2^l : ℤ), by simp,
        rw h, clear h,
        rwa [int.cast_le] },
      { apply pow_pos, norm_num } },
    -- The original proof uses x / 2^n ≤ (2^n - 1) / 2^n; use `< 1` is simpler.
    have hlt₂ : (x : ℚ) / 2^n < 1,
    { rw div_lt_one,
      { have h : (2^n : ℚ) = ((2^n : ℕ) : ℚ), by simp,
        rw h, clear h,
        rwa [nat.cast_lt], },
      { apply pow_pos, norm_num } },
    have hle₃ : (r : ℚ) / y ≤ 1 - 1 / y,
    { rw [one_sub_div hy'],
      mono, { simp },
      { have h : (y - 1 : ℚ) = (y - 1 : ℤ), by simp,
        rw h, clear h,
        rwa [int.cast_le] } },

    have h : 1 = 1 * 1 * (1 / (y : ℚ)) + (1 - 1 / y), by simp,
    conv_rhs { rw h }, clear h,
    mono right,

    have hinv_y_pos : 0 < 1 / (y : ℚ),
    { rw [one_div_pos, nat.cast_pos],
      apply nat.pos_of_ne_zero hy },
    mono, clear hinv_y_pos,

    have hx_div_pow2_nonneg : 0 ≤ (x : ℚ) / 2^n,
    { apply div_nonneg,
      { simp },
      { exact pow_nonneg dec_trivial _ } },
    mono left, norm_num },

  have h := int.floor_eq_iff.2 (and.intro hsub_lo hsub_hi),
  rw [rat.floor_int_div_nat_eq_div] at h,
  simp only [q] at h,
  zify, rw [← h], simp
end

-- Figure 4.1, without considering overflows (thus not using two shifts).
theorem div_eq_reciprocal_mul_div {n l x y : ℕ} :
  let m' := 2^n * (2^l - y) / y + 1,
      t₁ := m' * x / 2^n in
  x < 2^n →
  1 < y →
  y < 2^n →
  y ≤ 2^l →
  2^l < 2 * y →
  x / y = (t₁ + x) / 2^l :=
begin
  intros _ _ hx hy_lo hy_hi hpow2_l_lo hpow2_l_hi,
  let m := m' + 2^n,
  have hm : m = 2^(n + l) / y + 1,
  { simp only [m, m'],
    conv_lhs { rw [add_assoc, add_comm 1, ← add_assoc] },
    rw [← nat.add_mul_div_left _ _ (lt_trans dec_trivial hy_lo)],
    congr' 2,
    rw [nat.mul_sub_left_distrib, pow_add, mul_comm y],
    apply nat.sub_add_cancel, mono; omega },
  have hmy_lo : 2^(n + l) ≤ m * y,
  { rw [hm, right_distrib, one_mul, mul_comm],
    transitivity y * (2 ^ (n + l) / y) + (y - 1),
    { rw [← nat.div_le_iff_le_mul_add_pred], omega },
    { mono, apply nat.sub_le } },
  have hmy_hi : m * y ≤ 2^(n + l) + 2^l,
  { simp only [hm, right_distrib, one_mul],
    mono,
    apply nat.div_mul_le_self },
  rw [div_eq_reciprocal_mul_div_of_reciprocal hx hmy_lo hmy_hi],
  simp only [m, t₁],
  rw [pow_add, ← nat.div_div_eq_div_mul, right_distrib, nat.add_mul_div_left],
  apply pow_pos, dec_trivial
end

end bv
