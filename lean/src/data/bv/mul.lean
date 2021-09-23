/-
Copyright (c) 2021 The UNSAT Group. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luke Nelson, Xi Wang
-/
import .basic

namespace bv
variable {n : ℕ}

lemma mul_head (v₁ v₂ : fin (n + 1) → bool) :
  (v₁ * v₂) 0 = v₁ 0 && v₂ 0 :=
begin
  simp only [has_mul.mul],
  simp only [bv.mul],
  simp only [to_nat_succ, of_nat, nat.test_bit, fin.coe_zero, nat.shiftr],
  cases v₁ 0; cases v₂ 0; simp
end

lemma mul_tail (v₁ v₂ : fin (n + 1) → bool) :
  fin.tail (v₁ * v₂) = fin.tail (λ i, v₁ i && v₂ 0) + fin.init v₁ * fin.tail v₂ :=
begin
  apply eq_of_to_nat_eq_to_nat,
  simp only [to_nat_tail, add_to_nat, mul_to_nat],
  conv_lhs { rw [to_nat_succ v₂] },
  simp only [to_nat_init, to_nat_tail],
  simp only [nat.bit_val, nat.div2_val],
  rw [pow_succ, ← nat.div_mod_eq_mod_mul_div, nat.add_mod_mod],
  have two_pos : 0 < 2 := dec_trivial,
  conv_lhs { rw [mul_comm, right_distrib, add_comm, mul_assoc, nat.add_mul_div_left _ _ two_pos] },
  conv_rhs { rw [mul_comm, nat.add_mod, nat.mul_mod, nat.mod_mod, ← nat.mul_mod, ← nat.add_mod] },
  congr,
  have h : (λ i : fin (n + 1), ff) = 0, by refl,
  cases v₂ 0; simp [h, zero_to_nat]
end

end bv
