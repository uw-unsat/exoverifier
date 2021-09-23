/-
Copyright (c) 2021 The UNSAT Group. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luke Nelson, Xi Wang
-/
import .basic
import misc.fin

namespace bv

theorem concat_zero {n₁ : ℕ} (v₁ : fin n₁ → bool) (v₂ : fin 0 → bool) :
  concat v₁ v₂ = v₁ :=
begin
  rw [← fin.list_of_fn_inj],
  simp [list_of_fn_concat]
end

theorem concat_cons {n₁ n₂ : ℕ} (v₁ : fin n₁ → bool) (b : bool) (v₂ : fin n₂ → bool) :
  concat v₁ (fin.cons b v₂) = fin.cons b (concat v₁ v₂) :=
begin
  rw [← fin.list_of_fn_inj],
  simp [list_of_fn_concat]
end

theorem to_nat_concat {n₁ : ℕ} {n₂ : ℕ} (v₁ : fin n₁ → bool) (v₂ : fin n₂ → bool) :
  to_nat (concat v₁ v₂) = to_nat v₂ + 2^n₂ * to_nat v₁ :=
begin
  revert n₁,
  induction n₂ with n₂ ih; intros,
  { simp [concat_zero] },
  { conv_lhs { rw [← fin.cons_self_tail v₂] },
    conv_rhs { rw [← fin.cons_self_tail v₂] },
    simp only [concat_cons, to_nat_cons, ih],
    simp only [nat.bit_val, pow_succ],
    ring }
end

section drop_take
variable {n : ℕ}

/-- Drop the lower i bits. -/
def drop (i : ℕ) (v : fin n → bool) : fin (n - i) → bool :=
λ ⟨x, h⟩, v ⟨x + i, by omega⟩

/-- Extract the lower i bits. -/
def take (i : ℕ) (v : fin n → bool) : fin (min i n) → bool :=
λ ⟨x, h⟩, v ⟨x, lt_of_lt_of_le h (min_le_right _ _)⟩

theorem list_of_fn_drop (i : ℕ) (v : fin n → bool) :
  list.of_fn (drop i v) = (list.of_fn v).drop i :=
begin
  apply list.ext,
  intro x,
  rw [list.nth_of_fn, list.of_fn_nth_val],
  simp only [drop],
  split_ifs with hlt,
  { rw [list.nth_drop, list.nth_of_fn, list.of_fn_nth_val],
    rw [dif_pos],
    { congr' 3, rw [add_comm] },
    { omega } },
  { symmetry,
    rw [list.nth_eq_none_iff, list.length_drop, list.length_of_fn],
    rwa [← not_lt] }
end

theorem list_of_fn_take (i : ℕ) (v : fin n → bool) :
  list.of_fn (take i v) = (list.of_fn v).take i :=
begin
  apply list.ext,
  intro x,
  rw [list.nth_of_fn, list.of_fn_nth_val],
  by_cases hlt : x < min i n,
  { rw [list.nth_take (lt_of_lt_of_le hlt (min_le_left _ _))],
    rw [dif_pos hlt, list.nth_of_fn, list.of_fn_nth_val],
    rw [dif_pos (lt_of_lt_of_le hlt (min_le_right _ _))],
    refl },
  { rw [dif_neg hlt],
    symmetry,
    rw [list.nth_eq_none_iff, list.length_take, list.length_of_fn],
    rwa [← not_lt] }
end

theorem concat_drop_take (i : ℕ) (v : fin n → bool) :
  concat (drop i v) (take i v) == v :=
begin
  rw fin.heq_fun_iff,
  swap, { simp [min_comm] },
  rintro ⟨x, hx⟩,
  simp only [concat],
  simp only [drop, take, fin.coe_mk],
  split_ifs; congr,
  have hle : i ≤ n, by omega,
  rw min_eq_left hle at h hx ⊢,
  omega
end

theorem to_nat_drop (i : ℕ) (v : fin n → bool) :
  to_nat (drop i v) = to_nat v / 2^i :=
begin
  cases lt_or_le i n with hlt hle,
  { rw [← bv.to_nat_eq_of_heq (by simp [min_comm]) (concat_drop_take i v)],
    rw [to_nat_concat],
    simp only [min_eq_left (le_of_lt hlt)],
    have two_pos : 0 < 2 := dec_trivial,
    rw [nat.add_mul_div_left _ _ (pow_pos two_pos _)],
    rw [nat.div_eq_of_lt, zero_add],
    apply lt_of_lt_of_le (to_nat_lt _) (pow_le_pow dec_trivial (min_le_left _ _)) },
  { rw [nat.div_eq_of_lt (lt_of_lt_of_le (to_nat_lt _) (pow_le_pow dec_trivial hle))],
    rw [← to_nat_zero fin.elim0],
    have hz : n - i = 0, by omega,
    congr,
    { exact hz },
    { rw fin.heq_fun_iff hz,
      rintro ⟨_, h⟩,
      simpa [hz] using h } }

end

theorem to_nat_take (i : ℕ) (v : fin n → bool) :
  to_nat (take i v) = to_nat v % 2^i :=
begin
  cases lt_or_le i n with hlt hle,
  { rw [← bv.to_nat_eq_of_heq (by simp [min_comm]) (concat_drop_take i v)],
    rw [to_nat_concat],
    simp only [min_eq_left (le_of_lt hlt)],
    rw [nat.add_mul_mod_self_left],
    rw nat.mod_eq_of_lt,
    apply lt_of_lt_of_le (to_nat_lt _) (pow_le_pow dec_trivial (min_le_left _ _)) },
  { rw nat.mod_eq_of_lt (lt_of_lt_of_le (to_nat_lt _) (pow_le_pow dec_trivial hle)),
    have h := min_eq_right hle,
    congr,
    { exact h },
    { rw fin.heq_fun_iff h,
      rintro ⟨x, _⟩,
      refl } }
end

end drop_take

end bv
