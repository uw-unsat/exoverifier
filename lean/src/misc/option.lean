/-
Copyright (c) 2021 The UNSAT Group. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luke Nelson, Xi Wang
-/
import data.option.basic

namespace option
variable {α : Type*}

@[simp]
theorem orelse_eq_none_iff {x y : option α} :
  (x <|> y) = none ↔ x = none ∧ y = none :=
by cases x; simp

section has_to_pexpr
variable [has_to_pexpr α]

private meta def to_pexpr' : option α → pexpr
| none     := ``(none)
| (some x) := ``(some %%x)

meta instance : has_to_pexpr (option α) := ⟨to_pexpr'⟩

end has_to_pexpr
end option
