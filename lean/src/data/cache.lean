/-
Copyright (c) 2021 The UNSAT Group. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luke Nelson, Xi Wang
-/
import data.trie.basic

/-- Type class for node cache. -/
class cache (α : out_param Type*) (β : Type*) :=
(insert : α → β → β × bool)

instance list_as_cache (α : Type*) [decidable_eq α] : cache α (list α) :=
⟨λ a l, if a ∈ l then (l, ff) else (a :: l, tt)⟩

instance trie_as_cache : cache pos_num (trie unit) :=
⟨λ a t, t.kinsert' a ()⟩

/-- Default cache type. -/
@[reducible]
def cache' : Type :=
trie unit

/-- Tactic for constructing a default cache. -/
meta def default_cache : tactic unit := do
`[exact (trie.nil : cache')]
