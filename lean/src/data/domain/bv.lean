/-
Copyright (c) 2021 The UNSAT Group. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luke Nelson, Xi Wang
-/
import .basic
import data.bv.basic

/--
An abstract domain for bitvector operations, for a fixed width.
Must have decidable γ, ≤, ⊔, and ⊤.
Additionally must implement bitvector transfer functions and inverse analyses.
-/
class bv_abstr (α : ℕ → Type) :=
  (to_has_γ {n : ℕ} : has_γ (fin n → bool) (α n))
  (to_has_decidable_γ {n : ℕ} : has_decidable_γ (fin n → bool) (α n))
  (to_abstr_le {n : ℕ} : abstr_le (fin n → bool) (α n))
  (to_abstr_top {n : ℕ} : abstr_top (fin n → bool) (α n))
  (to_abstr_meet {n : ℕ} : abstr_meet (fin n → bool) (α n) (with_bot (α n)))
  (to_abstr_join {n : ℕ} : abstr_join (fin n → bool) (α n) (α n))

  (const {n : ℕ} (c : fin n → bool) :
    abstr_nullary_relation (= c) (α n))

  (not {n : ℕ} : abstr_unary_transfer bv.not (α n) (α n))
  (neg {n : ℕ} : abstr_unary_transfer bv.neg (α n) (α n))

  (add {n : ℕ} : abstr_binary_transfer (+) (α n) (α n) (α n))
  (sub {n : ℕ} : abstr_binary_transfer (λ x y, x - y) (α n) (α n) (α n))
  (and {n : ℕ} : abstr_binary_transfer bv.and (α n) (α n) (α n))
  (or {n : ℕ} : abstr_binary_transfer bv.or (α n) (α n) (α n))
  (xor {n : ℕ} : abstr_binary_transfer bv.xor (α n) (α n) (α n))
  (mul {n : ℕ} : abstr_binary_transfer bv.mul (α n) (α n) (α n))

  (udiv {n : ℕ} : abstr_binary_transfer bv.udiv (α n) (α n) (α n))
  (urem {n : ℕ} : abstr_binary_transfer bv.urem (α n) (α n) (α n))

  (shl {n m : ℕ} : abstr_binary_transfer bv.shl (α n) (α m) (α n))
  (lshr {n m : ℕ} : abstr_binary_transfer bv.lshr (α n) (α m) (α n))
  (ashr {n m : ℕ} : abstr_binary_transfer bv.ashr (α n) (α m) (α n))

namespace bv_abstr
variables {α : ℕ → Type} [self : bv_abstr α] {n : ℕ}
include self

instance : has_γ (fin n → bool) (α n) := bv_abstr.to_has_γ
instance : has_decidable_γ (fin n → bool) (α n) := bv_abstr.to_has_decidable_γ
instance : abstr_le (fin n → bool) (α n) := bv_abstr.to_abstr_le
instance : abstr_join (fin n → bool) (α n) (α n) := bv_abstr.to_abstr_join
instance : abstr_meet (fin n → bool) (α n) (with_bot (α n)) := bv_abstr.to_abstr_meet
instance : abstr_top (fin n → bool) (α n) := bv_abstr.to_abstr_top

instance : has_add (α n) := ⟨bv_abstr.add.op⟩

-- def gt : abstr_binary_inversion (fin n → bool) α (with_bot α) (>) :=
-- abstr_binary_inversion.invert_swap lt

-- def le : abstr_binary_inversion (fin n → bool) α (with_bot α) (≤) :=
-- begin
--   convert abstr_binary_inversion.invert_disjunction bv_abstr.eq bv_abstr.lt,
--   { ext x y,
--     rw [le_iff_eq_or_lt] },
--   apply_instance
-- end

-- def ge : abstr_binary_inversion (fin n → bool) α (with_bot α) (≥) :=
-- abstr_binary_inversion.invert_swap le

end bv_abstr
