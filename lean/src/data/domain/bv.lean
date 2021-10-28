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
class abstr_bv (α : ℕ → Type) :=
  (to_has_γ {n : ℕ} : has_γ (fin n.succ → bool) (α n.succ))
  (to_has_decidable_γ {n : ℕ} : has_decidable_γ (fin n.succ → bool) (α n.succ))
  (to_abstr_le {n : ℕ} : abstr_le (fin n.succ → bool) (α n.succ))
  (to_abstr_top {n : ℕ} : abstr_top (fin n.succ → bool) (α n.succ))
  (to_abstr_meet {n : ℕ} : abstr_meet (fin n.succ → bool) (α n.succ) (with_bot (α n.succ)))
  (to_abstr_join {n : ℕ} : abstr_join (fin n.succ → bool) (α n.succ) (α n.succ))

  (const {n : ℕ} (c : fin n.succ → bool) :
    abstr_nullary_relation (= c) (α n.succ))

  (not {n : ℕ} : abstr_unary_transfer bv.not (α n.succ) (α n.succ))
  (neg {n : ℕ} : abstr_unary_transfer bv.neg (α n.succ) (α n.succ))

  (add {n : ℕ} : abstr_binary_transfer (+) (α n.succ) (α n.succ) (α n.succ))
  (sub {n : ℕ} : abstr_binary_transfer (λ x y, x - y) (α n.succ) (α n.succ) (α n.succ))
  (and {n : ℕ} : abstr_binary_transfer bv.and (α n.succ) (α n.succ) (α n.succ))
  (or {n : ℕ} : abstr_binary_transfer bv.or (α n.succ) (α n.succ) (α n.succ))
  (xor {n : ℕ} : abstr_binary_transfer bv.xor (α n.succ) (α n.succ) (α n.succ))
  (mul {n : ℕ} : abstr_binary_transfer bv.mul (α n.succ) (α n.succ) (α n.succ))

  (udiv {n : ℕ} : abstr_binary_transfer bv.udiv (α n.succ) (α n.succ) (α n.succ))
  (urem {n : ℕ} : abstr_binary_transfer bv.urem (α n.succ) (α n.succ) (α n.succ))

  (shl {n m : ℕ} : abstr_binary_transfer bv.shl (α n.succ) (α m.succ) (α n.succ))
  (lshr {n m : ℕ} : abstr_binary_transfer bv.lshr (α n.succ) (α m.succ) (α n.succ))
  (ashr {n m : ℕ} : abstr_binary_transfer bv.ashr (α n.succ) (α m.succ) (α n.succ))

namespace abstr_bv
variables {α : ℕ → Type} [self : abstr_bv α] {n : ℕ}
include self

instance : has_γ (fin n.succ → bool) (α n.succ) := abstr_bv.to_has_γ
instance : has_decidable_γ (fin n.succ → bool) (α n.succ) := abstr_bv.to_has_decidable_γ
instance : abstr_le (fin n.succ → bool) (α n.succ) := abstr_bv.to_abstr_le
instance : abstr_join (fin n.succ → bool) (α n.succ) (α n.succ) := abstr_bv.to_abstr_join
instance : abstr_meet (fin n.succ → bool) (α n.succ) (with_bot (α n.succ)) := abstr_bv.to_abstr_meet
instance : abstr_top (fin n.succ → bool) (α n.succ) := abstr_bv.to_abstr_top

instance : has_add (α n.succ) := ⟨abstr_bv.add.op⟩

-- def gt : abstr_binary_inversion (fin n.succ → bool) α (with_bot α) (>) :=
-- abstr_binary_inversion.invert_swap lt

-- def le : abstr_binary_inversion (fin n.succ → bool) α (with_bot α) (≤) :=
-- begin
--   convert abstr_binary_inversion.invert_disjunction abstr_bv.eq abstr_bv.lt,
--   { ext x y,
--     rw [le_iff_eq_or_lt] },
--   apply_instance
-- end

-- def ge : abstr_binary_inversion (fin n.succ → bool) α (with_bot α) (≥) :=
-- abstr_binary_inversion.invert_swap le

end abstr_bv
