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
class bv_abstr (n : out_param ℕ) (α : Type)
  extends has_decidable_γ (fin n → bool) α,
          abstr_le (fin n → bool) α,
          abstr_top (fin n → bool) α,
          abstr_meet (fin n → bool) α (with_bot α),
          abstr_join (fin n → bool) α α : Type :=
  (const (c : fin n → bool) : abstr_nullary_relation (fin n → bool) α (eq c))
  (neg  : abstr_unary_transfer (fin n → bool) (fin n → bool) α α bv.neg)
  (add  : abstr_binary_transfer (fin n → bool) (fin n → bool) α α (+))
  (and  : abstr_binary_transfer (fin n → bool) (fin n → bool) α α bv.and)
  (ashr : abstr_binary_transfer (fin n → bool) (fin n → bool) α α bv.ashr)
  (lshr : abstr_binary_transfer (fin n → bool) (fin n → bool) α α bv.lshr)
  (mul  : abstr_binary_transfer (fin n → bool) (fin n → bool) α α (*))
  (or   : abstr_binary_transfer (fin n → bool) (fin n → bool) α α bv.or)
  (shl  : abstr_binary_transfer (fin n → bool) (fin n → bool) α α bv.shl)
  (udiv : abstr_binary_transfer (fin n → bool) (fin n → bool) α α (/))
  (urem : abstr_binary_transfer (fin n → bool) (fin n → bool) α α (%))
  (xor  : abstr_binary_transfer (fin n → bool) (fin n → bool) α α bv.xor)
  (eq   : abstr_binary_inversion (fin n → bool) α (with_bot α) (=))
  (lt   : abstr_binary_inversion (fin n → bool) α (with_bot α) (<))

namespace bv_abstr
variables {n : ℕ} {α : Type} [self : bv_abstr n α]
include self

instance : has_add α := ⟨bv_abstr.add.op⟩

def gt : abstr_binary_inversion (fin n → bool) α (with_bot α) (>) :=
abstr_binary_inversion.invert_swap lt

def le : abstr_binary_inversion (fin n → bool) α (with_bot α) (≤) :=
begin
  convert abstr_binary_inversion.invert_disjunction bv_abstr.eq bv_abstr.lt,
  { ext x y,
    rw [le_iff_eq_or_lt] },
  apply_instance
end

def ge : abstr_binary_inversion (fin n → bool) α (with_bot α) (≥) :=
abstr_binary_inversion.invert_swap le

end bv_abstr
