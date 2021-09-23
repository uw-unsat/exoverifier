/-
Copyright (c) 2021 The UNSAT Group. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luke Nelson, Xi Wang
-/

/--
Types that can be reified from meta lean to regular lean. `has_reflect` is too weak
bceause it requires the expression to be type-correct. An example is reifying `vector`
from meta lean to object lean: we cannot reflect it because it contains proofs,
but we can reify it by converting to list in meta lean and checking the length in regular lean.

This cannot be a meta-definition since deserialization must be performed in regular lean.
-/
class has_serialize (α : Type*) (β : out_param Type) :=
(serialize   : α → β)
(deserialize : β → α)

/--
If an type is reflectable, then it is reifiable via itself.
Only use for types that have a `has_reflect` instance.
-/
def serialize_via_id {α : Type} : has_serialize α α :=
⟨ id, id ⟩

/--
Reify a functor. Only use when the functor type has a `has_reflect` instance.
-/
def serialize_functor {f : Type* → Type} [functor f] {α : Type*} {α' : Type} [has_serialize α α'] :
  has_serialize (f α) (f α') :=
⟨ λ (l : f α), has_serialize.serialize <$> l,
  λ (l : f α'), has_serialize.deserialize <$> l ⟩


-- These instances are fine because these types are already serializable via reflection.
instance : has_serialize bool bool := serialize_via_id
instance : has_serialize ℕ ℕ := serialize_via_id

section
variables {α : Type} {α' : Type} [has_serialize α α']

-- Serialize lists by serializing elements.
instance : has_serialize (list α) (list α') := serialize_functor

end
