/-
Copyright (c) 2021 The UNSAT Group. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luke Nelson, Xi Wang
-/
import .basic

namespace bv
variable {n : ℕ}

/-- Add with carry. -/
protected def adc (v₁ v₂ : fin n → bool) (c : bool) : fin n → bool :=
v₁ + v₂ + cond c 1 0

/-- Overflow checking for add with carry. -/
def adc_overflow (v₁ v₂ : fin n → bool) (c : bool) : Prop :=
2^ n ≤ to_nat v₁ + to_nat v₂ + cond c 1 0

instance : ∀ (v₁ v₂ : fin n → bool) (c : bool), decidable (adc_overflow v₁ v₂ c) :=
λ _ _ _, by { dsimp [adc_overflow], apply_instance }

theorem adc_eq_of_nat (v₁ v₂ : fin n → bool) (c : bool) :
  bv.adc v₁ v₂ c = bv.of_nat (bv.to_nat v₁ + bv.to_nat v₂ + cond c 1 0) :=
begin
  cases n,
  { apply subsingleton.elim },
  { apply eq_of_to_nat_eq_to_nat,
    simp only [bv.adc, add_to_nat, to_of_nat, nat.mod_add_mod],
    cases c; simp [zero_to_nat, one_to_nat] }
end

theorem adc_zero (v₁ v₂ : fin (n + 1) → bool) (c : bool) :
  bv.adc v₁ v₂ c 0 = bxor (bxor (v₁ 0) (v₂ 0)) c :=
begin
  rw [adc_eq_of_nat],
  simp only [of_nat, fin.coe_zero, nat.test_bit, nat.shiftr],
  simp only [nat.bodd_add, nat.bodd_bit, to_nat_succ],
  cases c; refl
end

theorem adc_succ (v₁ v₂ : fin (n + 1) → bool) (c : bool) : ∀ i,
  bv.adc v₁ v₂ c (fin.succ i) =
  bv.adc (fin.tail v₁) (fin.tail v₂) (((v₁ 0) && (v₂ 0)) || (c && (bxor (v₁ 0) ((v₂ 0))))) i :=
begin
  intro i,
  simp only [adc_eq_of_nat],
  simp only [of_nat, nat.test_bit],
  rw fin.coe_succ, rw add_comm ↑i 1,
  rw nat.shiftr_add,
  congr' 2,
  simp only [nat.shiftr, nat.div2_val],
  have h : to_nat v₁ + to_nat v₂ + cond c 1 0 =
             cond (v₁ 0) 1 0 + cond (v₂ 0) 1 0 + cond c 1 0 +
             2 * (to_nat (fin.tail v₁) + to_nat (fin.tail v₂)),
  { simp only [to_nat_succ, nat.bit_val], ring },
  rw [h], clear h,
  rw [nat.add_mul_div_left _ _ (show 0 < 2, from dec_trivial)],
  conv_lhs { rw [add_comm] },
  congr' 1,
  cases v₁ 0; cases v₂ 0; cases c; refl
end

theorem adc_overflow_succ (v₁ v₂ : fin (n + 1) → bool) (c : bool) :
  adc_overflow v₁ v₂ c ↔
  adc_overflow (fin.tail v₁) (fin.tail v₂) (v₁ 0 && v₂ 0 || c && bxor (v₁ 0) (v₂ 0)) :=
begin
  simp only [adc_overflow],
  rw [pow_succ, ← nat.bit0_val],
  have h : to_nat v₁ + to_nat v₂ = 2 * (to_nat (fin.tail v₁) + to_nat (fin.tail v₂)) + cond (v₁ 0) 1 0 + cond (v₂ 0) 1 0,
  { simp only [to_nat_succ, nat.bit_val], ring },
  rw h, clear h,
  have add1_2 : ∀ (x : ℕ), x + 1 + 1 = x + 2 * 1, by simp,
  have add1_3 : ∀ (x : ℕ), x + 1 + 1 + 1 = x + 2 * 1 + 1, by simp,
  cases v₁ 0; cases v₂ 0; cases c;
  simp only [add_zero, band, bor, bxor, cond];
  try { rw [add1_3] <|> rw [add1_2] };
  try { rw [← left_distrib] };
  try { rw [← nat.bit1_val] <|> rw [← nat.bit0_val] };
  simp
end

theorem add_eq_adc (v₁ v₂ : fin n → bool) :
  v₁ + v₂ = bv.adc v₁ v₂ ff :=
by simp only [bv.adc, cond, add_zero]

end bv
