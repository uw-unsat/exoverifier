/-
Copyright (c) 2021 The UNSAT Group. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luke Nelson, Xi Wang
-/
import data.option.basic
import order.bounded_order

namespace option
variables (α β : Type*)

instance : partial_order (α → option β) :=
{ le          := λ x y, ∀ {a : α} {b : β}, x a = some b → y a = some b,
  le_refl     := λ _, by tauto,
  le_trans    := λ _ _ _, by tauto,
  le_antisymm := λ _ _ _ _, by ext; tauto}

instance : order_bot (α → option β) :=
{ bot         := λ _, none,
  bot_le      := λ _ _ _, by simp }

end option
