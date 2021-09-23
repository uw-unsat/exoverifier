/-
Copyright (c) 2021 The UNSAT Group. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luke Nelson, Xi Wang
-/
import .adc

namespace bv
variable {n : ℕ}

/-- Subtract with carry. -/
protected def sbc (v₁ v₂ : fin n → bool) (c : bool) : fin n → bool :=
v₁ - v₂ - cond c 0 1

/-- Overflow checking for subtract with carry. -/
def sbc_overflow (v₁ v₂ : fin n → bool) (c : bool) : Prop :=
to_nat v₁ < to_nat v₂ + cond c 0 1

instance : ∀ (v₁ v₂ : fin n → bool) (c : bool), decidable (sbc_overflow v₁ v₂ c) :=
λ _ _ _, by { dsimp [sbc_overflow], apply_instance }

theorem sbc_eq_adc (v₁ v₂ : fin n → bool) (c : bool) :
  bv.sbc v₁ v₂ c = bv.adc v₁ (bv.not v₂) c :=
begin
  cases n, { apply subsingleton.elim },
  simp only [bv.sbc],
  have h : v₁ - v₂ = v₁ + bv.not v₂ + 1,
  { rw [add_assoc, ← neg_eq_not_add_one], refl },
  rw h, clear h,
  apply eq_of_to_nat_eq_to_nat,
  cases c; simp only [bv.adc, cond, add_sub_cancel, add_zero, sub_zero];
  simp [add_to_nat, one_to_nat, to_of_nat]
end

theorem sbc_overflow_iff_not_adc_overflow (v₁ v₂ : fin n → bool) (c : bool) :
  sbc_overflow v₁ v₂ c ↔ ¬ adc_overflow v₁ (bv.not v₂) c :=
begin
  simp only [adc_overflow, sbc_overflow, not_to_nat, not_le],
  have h₁ := to_nat_lt v₁,
  have h₂ := to_nat_lt v₂,
  cases c; omega
end

theorem sub_eq_sbc (v₁ v₂ : fin n → bool) :
  v₁ - v₂ = bv.sbc v₁ v₂ tt :=
by simp only [bv.sbc, cond, sub_zero]

end bv
