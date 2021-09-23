/-
Copyright (c) 2021 The UNSAT Group. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luke Nelson, Xi Wang
-/
import .factory
import factory.interface
import logic.nontrivial

namespace sat

/-- Trivial const instance for booleans as expressions. -/
instance : const_factory bool punit :=
{ mk_const     := λ _, id,
  sat_mk_const := by {
    intros _ _,
    exact rfl } }

/-- Trivial and instance for booleans as expressions. -/
instance : and_factory bool punit :=
{ mk_and     := λ x y, pure (x && y),
  le_mk_and  := λ _ _ _, subsingleton.le _ _,
  sat_mk_and := by {
    rintros _ _ _ _ _ _ _ ⟨⟩ ⟨⟩ ⟨⟩,
    exact rfl } }

/-- Trivial or instance for booleans as expressions. -/
instance : or_factory bool punit :=
{ mk_or     := λ x y, pure (x || y),
  le_mk_or  := λ _ _ _, subsingleton.le _ _,
  sat_mk_or := by {
    rintros _ _ _ _ _ _ _ ⟨⟩ ⟨⟩ ⟨⟩,
    exact rfl } }

/-- Trivial not instance for booleans as expressions. -/
instance : not_factory bool punit :=
{ mk_not     := λ x, pure (!x),
  le_mk_not  := λ _ _, subsingleton.le _ _,
  sat_mk_not := by {
    rintros _ _ _ _ _ ⟨⟩ ⟨⟩,
    exact rfl } }

end sat
