/-
Copyright (c) 2021 The UNSAT Group. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luke Nelson, Xi Wang
-/
import order.bounded_lattice
import misc.reify

namespace with_bot
section
variable {T : Type*}

/- Allow with_bot to behave like a functor/applicative/monad via `option`. -/
local attribute [reducible] with_bot

instance : functor with_bot           := by apply_instance
instance : is_lawful_functor with_bot := by apply_instance

instance : applicative with_bot           := by apply_instance
instance : is_lawful_applicative with_bot := by apply_instance

instance : monad with_bot           := by apply_instance
instance : is_lawful_monad with_bot := by apply_instance

instance [has_repr T] : has_repr (with_bot T) :=
⟨λ r,
  match r with
  | some x := repr x
  | none := "⊥"
  end⟩

section
variables {α : Type} {α' : Type} [has_serialize α α']
instance : has_serialize (with_bot α) (with_bot α') := serialize_functor
end

end
end with_bot
