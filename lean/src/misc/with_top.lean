/-
Copyright (c) 2021 The UNSAT Group. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luke Nelson, Xi Wang
-/
import order.bounded_order
import misc.option

namespace with_top
section
variable {T : Type*}

/- Allow with_top to behave like a functor/applicative/monad via `option`. -/
local attribute [reducible] with_top

instance : functor with_top           := by apply_instance
instance : is_lawful_functor with_top := by apply_instance

instance : applicative with_top           := by apply_instance
instance : is_lawful_applicative with_top := by apply_instance

instance : monad with_top           := by apply_instance
instance : is_lawful_monad with_top := by apply_instance

instance [has_repr T] : has_repr (with_top T) :=
⟨λ r,
  match r with
  | some x := repr x
  | none := "⊤"
  end⟩

meta instance [has_to_pexpr T] : has_to_pexpr (with_top T) := by apply_instance

end
end with_top
