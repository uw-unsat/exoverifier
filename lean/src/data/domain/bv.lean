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
  (add : abstr_binary_transfer (fin n → bool) α α bv.add)
  (and : abstr_binary_transfer (fin n → bool) α α bv.and)
  (or  : abstr_binary_transfer (fin n → bool) α α bv.or)
  (xor : abstr_binary_transfer (fin n → bool) α α bv.xor)
  (eq  : abstr_binary_inversion (fin n → bool) α (with_bot α) eq)

namespace bv_abstr
variables (n : ℕ) (α : Type)
instance [bv_abstr n α] : has_add α := ⟨bv_abstr.add.op⟩
end bv_abstr
