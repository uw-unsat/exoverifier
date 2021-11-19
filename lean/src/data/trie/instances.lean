/-
Copyright (c) 2021 The UNSAT Group. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luke Nelson, Xi Wang
-/
import .basic
import control.traversable.instances

namespace trie

section functor
variables {α β : Type*}

/-- Map a function over each value in the trie.
    Performs no simplifications (as these would violate the functor laws.) -/
protected def fmap (f : α → β) : trie α → trie β
| nil          := nil
| (node a l r) := node (option.map f a) l.fmap r.fmap

instance : functor trie :=
{ map := @trie.fmap }

instance : is_lawful_functor trie :=
{ id_map := by {
  intros _ x,
  induction x,
  case nil : { refl },
  case node : x l r ih_l ih_r {
    simp only [functor.map, trie.fmap] at ih_l ih_r ⊢,
    rw [ih_l, ih_r],
    simp } },
  comp_map := by {
    intros _ _ _ _ _ x,
    induction x,
    case nil : { refl },
    case node : x l r ih_l ih_r {
      simp only [functor.map, trie.fmap] at ih_l ih_r ⊢,
      rw [ih_l, ih_r],
      simp } } }

end functor

section traversable
universe u
variables {m : Type u → Type u} [applicative m] {α β : Type u}

def traverse (f : α → m β) : trie α → m (trie β)
| nil          := pure nil
| (node a l r) := node <$> traversable.traverse f a <*> traverse l <*> traverse r

instance traversable' : traversable trie :=
{ traverse := @traverse }

theorem traverse_def {f : α → m β} {t : trie α} :
  traversable.traverse f t = trie.traverse f t :=
by refl

instance : is_lawful_traversable trie :=
{ id_traverse := by {
  intros _ x,
  induction x,
  case nil : { refl },
  case node : x l r ih_l ih_r {
    simp only [traversable.traverse, trie.traverse] at ih_l ih_r ⊢,
    rw [ih_l, ih_r],
    cases x; refl } },
  comp_traverse := by {
    intros _ _ _ _ _ _ _ _ _ _ _ x,
    resetI,
    induction x,
    case nil : {
      simp only [traverse_def, trie.traverse, is_lawful_applicative.map_pure, functor.comp.mk],
      refl },
    case node : x l r ih_l ih_r {
      simp only [traverse_def, trie.traverse] at ih_l ih_r ⊢,
      rw [ih_l, ih_r], clear ih_l, clear ih_r,
      simp only [is_lawful_traversable.comp_traverse],
      simp with functor_norm,
      refl } },
  traverse_eq_map_id := by {
    intros _ _ _ x,
    resetI,
    induction x,
    case nil : { refl },
    case node : x l r ih_l ih_r {
      simp only [traverse_def, trie.traverse] at ih_l ih_r ⊢,
      rw [ih_l, ih_r], clear ih_l, clear ih_r,
      simp only [is_lawful_traversable.traverse_eq_map_id],
      refl } },
  naturality := by {
    intros _ _ _ _ _ _ _ _ _ _ x,
    resetI,
    induction x,
    case nil : {
      simp only [traverse_def, trie.traverse, applicative_transformation.preserves_pure] },
    case node : x l r ih_l ih_r {
      simp only [traverse_def, trie.traverse, applicative_transformation.preserves_seq] at ih_l ih_r ⊢,
      rw [ih_l, ih_r],
      simp with functor_norm } } }

end traversable
end trie
