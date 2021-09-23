/-
Copyright (c) 2021 The UNSAT Group. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luke Nelson, Xi Wang
-/
import .basic

/-!
# Bitvectors and integers

This file provides lemmas between bitvectors and ℤ as sanity checks.
-/

namespace bv
variable {n : ℕ}

/-- Convert an integer to a bitvector. -/
def of_int (a : ℤ) : fin n → bool :=
bv.of_nat (a % (2^n)).to_nat

/-- Convert a bitvector to an integer. -/
def to_int (v : fin n → bool) : ℤ :=
if bv.to_nat v < 2^(n - 1) then bv.to_nat v else bv.to_nat v - 2^n

theorem of_to_int (v : fin n → bool) :
  bv.of_int (bv.to_int v) = v :=
begin
  simp only [of_int, to_int],
  apply eq_of_to_nat_eq_to_nat,
  rw [to_of_nat],
  have hlt := to_nat_lt v,
  zify at hlt ⊢,
  split_ifs;
  try { rw [int.sub_mod] };
  simp [int.mod_eq_of_lt (int.coe_nat_nonneg _) hlt]
end

theorem to_int_inj (v₁ v₂ : fin n → bool) :
  bv.to_int v₁ = bv.to_int v₂ ↔ v₁ = v₂ :=
⟨λ h, function.left_inverse.injective of_to_int h, congr_arg _⟩

@[simp]
theorem to_int_zero (v : fin 0 → bool) :
  to_int v = 0 :=
by simp [to_int]

theorem neg_to_int (v : fin n → bool) :
  to_int (-v) = if to_int v = -2^(n - 1) then -2^(n - 1) else -to_int v :=
begin
  have htwo : ((2 : ℕ) : ℤ) = (2 : ℤ) := dec_trivial,
  cases n, { simp },
  split_ifs with h,
  { simp only [to_int, neg_to_nat, nat.succ_sub_one] at h ⊢,
    zify at h ⊢,
    simp only [int.coe_nat_sub (le_of_lt (to_nat_lt _))],
    simp only [pow_succ, int.coe_nat_mul, int.coe_nat_pow, htwo] at h ⊢,
    split_ifs at h with h₁,
    { exfalso,
      have h₁ : (to_nat v : ℤ) < 0,
      { rw [h, neg_neg_iff_pos],
        apply pow_pos, dec_trivial },
      simpa [lt_iff_not_ge] using h₁ },
    { split_ifs; linarith } },
  simp only [to_int, neg_to_nat, nat.succ_sub_one] at h ⊢,
  by_cases h₁ : to_nat v = 0,
  { have hne := ne_of_gt (pow_pos (show 0 < 2, by dec_trivial) n),
    zify at hne,
    simp [h₁, hne] },
  { simp only [h₁, if_false],
    zify at h h₁ ⊢,
    simp only [int.coe_nat_sub (le_of_lt (to_nat_lt _))],
    simp only [pow_succ] at h ⊢,
    simp only [int.coe_nat_mul, int.coe_nat_pow],
    simp only [htwo],
    split_ifs with h₂ h₃ h₄,
    { linarith },
    { linarith },
    { linarith },
    { simp only [h₄, if_false] at h,
      exfalso, contrapose! h,
      linarith } }
end

theorem msb_eq_ff_iff (v : fin n → bool) :
  bv.msb v = ff ↔ bv.to_nat v < 2^(n - 1) :=
begin
  cases n, { simp },
  conv_rhs { rw [← fin.snoc_init_self v] },
  simp only [to_nat_snoc, to_nat_init, msb],
  have h₁ : to_nat v % 2^n < 2^n := nat.mod_lt (bv.to_nat _) (pow_pos dec_trivial _),
  cases v (fin.last n); simp [h₁]
end

theorem slt_to_int (v₁ v₂ : fin n → bool) :
  bv.to_int v₁ < bv.to_int v₂ ↔ bv.slt v₁ v₂ :=
begin
  simp only [bv.slt, to_int, ← msb_eq_ff_iff],
  conv_rhs { simp only [has_lt.lt] },
  simp only [bv.ult],
  have h₁ := to_nat_lt v₁,
  have h₂ := to_nat_lt v₂,
  zify at h₁ h₂,
  cases h₃ : bv.msb v₁; cases h₄ : bv.msb v₂; simp only [h₃, h₄],
  { simp },
  { suffices : ¬(to_nat v₁ : ℤ) < (to_nat v₂ : ℤ) - 2^n, by simpa,
    linarith },
  { suffices : (to_nat v₁ : ℤ) - 2^n < (to_nat v₂ : ℤ), by simpa,
    linarith },
  { simp }
end

theorem sle_to_int (v₁ v₂ : fin n → bool) :
  bv.to_int v₁ ≤ bv.to_int v₂ ↔ bv.sle v₁ v₂ :=
by rw [le_iff_eq_or_lt, to_int_inj, slt_to_int, bv.sle_iff_eq_or_slt]

end bv
