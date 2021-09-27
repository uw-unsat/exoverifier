/-
Copyright (c) 2021 The UNSAT Group. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luke Nelson, Xi Wang
-/
import data.num.lemmas
import misc.list
import misc.option

/-!
# Binary trie

This file provides a binary trie using `pos_num`, optimized for in-kernel computation.

## Implementation notes

This is similar to `data.tree`, but it stores `option` values in nodes to allow operations such as
insert or erase.

A trie processes the bits of each key in little-endian order. The result of `trie.to_list` is thus
not sorted by keys.

## References

* Chris Okasaki and Andrew Gill. *Fast Mergeable Integer Maps*.
  <https://citeseerx.ist.psu.edu/viewdoc/summary?doi=10.1.1.37.5452>
-/

/-- A binary trie. -/
@[derive [decidable_eq, has_reflect]]
inductive trie (α : Type*)
| nil  : trie
| node : option α → trie → trie → trie

namespace trie
universe u
variables {α : Type u}

instance : inhabited (trie α) :=
⟨nil⟩

instance : has_emptyc (trie α) :=
⟨nil⟩

section has_to_pexpr
variable [has_to_pexpr α]

meta def to_pexpr' : trie α → pexpr
| nil          := ``(trie.nil)
| (node x l r) := ``(node %%x %%(to_pexpr' l) %%(to_pexpr' r))

meta instance : has_to_pexpr (trie α) := ⟨to_pexpr'⟩

end has_to_pexpr

section repr
variable [has_repr α]

private def repr_aux : ℕ → trie α → list string
| _ nil          := ["nil"]
| n (node o l r) := let f := λ (r : list string) (ph pt : string),
                             "|" :: (ph ++ r.head) :: r.tail.map (λ s, pt ++ s) in
  match o with
  | none   := "+"
  | some a := has_repr.repr a
  end ::
  match l, r with
  | nil, nil := []
  | _,   _   := f (repr_aux (n + 1) l) "0- " "|  " ++ f (repr_aux (n + 1) r) "1- " "   "
  end

private def repr (t : trie α) : string :=
"\n".intercalate (repr_aux 0 t)

instance : has_repr (trie α) :=
⟨repr⟩

end repr

section to_list

/-- Prepend `bit0` to each `pos_num` key. -/
@[reducible]
def map_bit0 (ns : list (Σ _ : pos_num, α)) : list (Σ _ : pos_num, α) :=
ns.map (λ s, ⟨s.1.bit0, s.2⟩)

/-- Prepend `bit1` to each `pos_num` key. -/
@[reducible]
def map_bit1 (ns : list (Σ _ : pos_num, α)) : list (Σ _ : pos_num, α) :=
ns.map (λ s, ⟨s.1.bit1, s.2⟩)

/-- Convert a trie to a list of key-value pairs. -/
def to_list : trie α → list (Σ _ : pos_num, α)
| nil                 := []
| (node none     l r) := map_bit0 l.to_list ++ map_bit1 r.to_list
| (node (some a) l r) := ⟨pos_num.one, a⟩ :: (map_bit0 l.to_list ++ map_bit1 r.to_list)

lemma nodupkeys_map_bit0 (ns : list (Σ _ : pos_num, α)) :
  (map_bit0 ns).nodupkeys ↔ ns.nodupkeys :=
begin
  conv_lhs { rw [list.nodupkeys_iff_pairwise, list.pairwise_map] },
  simp [list.nodupkeys_iff_pairwise]
end

lemma nodupkeys_map_bit1 (ns : list (Σ _ : pos_num, α)) :
  (map_bit1 ns).nodupkeys ↔ ns.nodupkeys :=
begin
  conv_lhs { rw [list.nodupkeys_iff_pairwise, list.pairwise_map] },
  simp [list.nodupkeys_iff_pairwise]
end

theorem nodupkeys_append {α : Type*} {β : α → Type*} {l₁ l₂ : list (sigma β)} :
  (l₁ ++ l₂).nodupkeys ↔ l₁.nodupkeys ∧ l₂.nodupkeys ∧ l₁.keys.disjoint l₂.keys :=
by { rw [list.nodupkeys, list.keys, list.map_append, list.nodup_append], refl }

section
variables {α₀ α₁ : Type*}

theorem map_bit0_bit1_disjoint_keys (ns₀ : list (Σ _ : pos_num, α₀))
                                    (ns₁ : list (Σ _ : pos_num, α₁)) :
  (map_bit0 ns₀).keys.disjoint (map_bit1 ns₁).keys :=
begin
  intros n hbit0 hbit1,
  have h₀ : ∃ (k : pos_num), (∃ (a : α₀), sigma.mk k a ∈ ns₀) ∧ k.bit0 = n,
  { simpa [list.keys] using hbit0 },
  have h₁ : ∃ (k : pos_num), (∃ (a : α₁), sigma.mk k a ∈ ns₁) ∧ k.bit1 = n,
  { simpa [list.keys] using hbit1 },
  rcases h₀ with ⟨a₀, _, _⟩,
  rcases h₁ with ⟨a₁, _, _⟩,
  cc
end

theorem map_keys_subset_map_keys_iff {f : pos_num → pos_num} (hinj : function.injective f)
                                     (ns₀ : list (Σ _ : pos_num, α₀))
                                     (ns₁ : list (Σ _ : pos_num, α₁)) :
  (ns₀.map (λ (s : (Σ _ : pos_num, α₀)), (⟨f s.1, s.2⟩ : (Σ _ : pos_num, α₀)))).keys ⊆
  (ns₁.map (λ (s : (Σ _ : pos_num, α₁)), (⟨f s.1, s.2⟩ : (Σ _ : pos_num, α₁)))).keys ↔
  ns₀.keys ⊆ ns₁.keys :=
begin
  suffices :
    (∀ {k : pos_num} {k₀ : pos_num} {a₀ : α₀},
       sigma.mk k₀ a₀ ∈ ns₀ →
       f k₀ = k →
       ∃ (k₁ : pos_num), (∃ (a₁ : α₁), sigma.mk k₁ a₁ ∈ ns₁) ∧ f k₁ = k) ↔
    (∀ {k : pos_num} {a₀ : α₀},
       sigma.mk k a₀ ∈ ns₀ →
       ∃ (a₁ : α₁), sigma.mk k a₁ ∈ ns₁),
  { simpa [list.keys, list.subset_def] },
  split,
  { intro h, intros k a ka,
    specialize h ka rfl,
    rcases h with ⟨k', h, k'k⟩,
    cases hinj k'k,
    exact h },
  { tauto }
end

theorem map_bit0_keys_subset_map_bit0_keys_iff : ∀ (ns₀ : list (Σ _ : pos_num, α₀))
                                                   (ns₁ : list (Σ _ : pos_num, α₁)),
  (map_bit0 ns₀).keys ⊆ (map_bit0 ns₁).keys ↔ ns₀.keys ⊆ ns₁.keys :=
@map_keys_subset_map_keys_iff _ _ pos_num.bit0 (λ _, by simp)

theorem map_bit1_keys_subset_map_bit1_keys_iff : ∀ (ns₀ : list (Σ _ : pos_num, α₀))
                                                   (ns₁ : list (Σ _ : pos_num, α₁)),
  (map_bit1 ns₀).keys ⊆ (map_bit1 ns₁).keys ↔ ns₀.keys ⊆ ns₁.keys :=
@map_keys_subset_map_keys_iff _ _ pos_num.bit1 (λ _, by simp)

end

lemma map_bit0_bit1_nodupkeys {ns₀ ns₁ : list (Σ _ : pos_num, α)} :
  ns₀.nodupkeys →
  ns₁.nodupkeys →
  (map_bit0 ns₀ ++ map_bit1 ns₁).nodupkeys :=
begin
  rw [nodupkeys_append, nodupkeys_map_bit0, nodupkeys_map_bit1],
  have h := map_bit0_bit1_disjoint_keys ns₀ ns₁,
  tauto
end

theorem one_not_mem_keys_map_bit0 (ns : list (Σ _ : pos_num, α)) :
pos_num.one ∉ (map_bit0 ns).keys :=
by simp [list.keys]

theorem one_not_mem_keys_map_bit1 (ns : list (Σ _ : pos_num, α)) :
pos_num.one ∉ (map_bit1 ns).keys :=
by simp [list.keys]

theorem one_not_mem_keys_append_map_bit0_map_bit1 (ns₀ ns₁ : list (Σ _ : pos_num, α)) :
pos_num.one ∉ (map_bit0 ns₀ ++ map_bit1 ns₁).keys :=
by simp [list.keys]

theorem to_list_nodupkeys : ∀ (t : trie α),
  t.to_list.nodupkeys
| nil                 := by { simp [to_list] }
| (node none     l r) := by { apply map_bit0_bit1_nodupkeys; tauto }
| (node (some a) l r) := by {
  apply list.nodupkeys_cons.2,
  split,
  { apply one_not_mem_keys_append_map_bit0_map_bit1 },
  { apply map_bit0_bit1_nodupkeys; tauto } }

end to_list

/-- Convert a trie to a list of values. -/
def elems : trie α → list α
| nil                 := []
| (node none     l r) := l.elems ++ r.elems
| (node (some a) l r) := a :: (l.elems ++ r.elems)

theorem mem_elems_iff : ∀ (t: trie α) (a : α),
  a ∈ t.elems ↔
  ∃ (k : pos_num), sigma.mk k a ∈ t.to_list
| nil := by simp [elems, to_list]
| (node none     l r) := λ a, by {
  simp only [elems, to_list, list.mem_append],
  simp only [list.mem_map, mem_elems_iff, heq_iff_eq],
  split,
  { rintro (⟨k, h⟩ | ⟨k, h⟩),
    { existsi k.bit0, left, existsi sigma.mk k a, simpa },
    { existsi k.bit1, right, existsi sigma.mk k a, simpa } },
  { rintro ⟨k, ⟨s, ⟨h₁, h₂, h₃⟩⟩ | ⟨s, ⟨h₁, h₂, h₃⟩⟩⟩,
    { left, existsi s.1, subst_vars, simpa },
    { right, existsi s.1, subst_vars, simpa } } }
| (node (some _) l r) := λ a, by {
  simp only [elems, to_list, list.mem_append, list.mem_cons_iff],
  simp only [list.mem_map, mem_elems_iff, heq_iff_eq],
  split,
  { rintro (h | ⟨k, h⟩ | ⟨k, h⟩),
    { existsi pos_num.one, left, simpa },
    { existsi k.bit0, right, left, existsi sigma.mk k a, simpa },
    { existsi k.bit1, right, right, existsi sigma.mk k a, simpa } },
  { rintro ⟨k, ⟨h₁, h₂⟩ | ⟨s, ⟨h₁, h₂, h₃⟩⟩ | ⟨s, ⟨h₁, h₂, h₃⟩⟩⟩,
    { left, assumption },
    { right, left, existsi s.1, subst_vars, simpa },
    { right, right, existsi s.1, subst_vars, simpa } } }

/-- Test whether a trie is empty. -/
def null : trie α → bool
| nil                 := tt
| (node none     l r) := l.null ∧ r.null
| (node (some _) _ _) := ff

theorem null_iff : ∀ (t : trie α),
  t.null ↔
  t.to_list = []
| nil                 := by simp [null, to_list]
| (node none     l r) := by {
  suffices : ↥(l.null) ∧ ↥(r.null) ↔ l.to_list = [] ∧ r.to_list = [],
  { simpa [null, to_list] },
  simp [null_iff] }
| (node (some _) _ _) := by simp [null, to_list]

/-- Extract the element if a trie is a singleton, otherwise return none. -/
def unsingleton : trie α → option (Σ _ : pos_num, α)
| nil                 := none
| (node none     l r) :=
  if l.null then do
    s ← r.unsingleton,
    some ⟨s.1.bit1, s.2⟩
  else if r.null then do
    s ← l.unsingleton,
    some ⟨s.1.bit0, s.2⟩
  else
    none
| (node (some a) l r) :=
  if l.null ∧ r.null then
    some ⟨pos_num.one, a⟩
  else
    none

lemma map_eq_singleton_iff_exists {α β : Type*} (f : α → β) (l : list α) (b : β) :
  l.map f = [b] ↔ ∃ (a : α), l = [a] ∧ f a = b :=
begin
  split,
  { cases l with hd tl,
    { simp },
    { simp only [list.map, list.map_eq_nil],
      tauto } },
  { rintro ⟨a, h₁, h₂⟩,
    rw [h₁, ← h₂],
    refl }
end

theorem unsingleton_iff : ∀ (t : trie α) (s : (Σ _ : pos_num, α)),
  t.unsingleton = some s ↔ t.to_list = [s]
| nil                 := by simp [unsingleton, to_list]
| (node none     l r) := λ _, by {
  simp only [unsingleton, to_list],
  split_ifs with hl hr,
  -- l = ∅
  { rw [l.null_iff.1 hl, map_bit0, list.map_nil, list.nil_append],
    simp only [option.bind_eq_some, r.unsingleton_iff],
    rw map_eq_singleton_iff_exists },
  -- l ≠ ∅ ∧ r = ∅
  { rw [r.null_iff.1 hr, map_bit1, list.map_nil, list.append_nil],
    simp only [option.bind_eq_some, l.unsingleton_iff],
    rw map_eq_singleton_iff_exists },
  -- l ≠ ∅ ∧ r ≠ ∅
  { rw false_iff,
    by_contra h,
    have hle₀ : 1 ≤ (map_bit0 l.to_list).length,
    { apply list.length_pos_of_ne_nil, rw null_iff at hl, simp [hl] },
    have hle₁ : 1 ≤ (map_bit1 r.to_list).length,
    { apply list.length_pos_of_ne_nil, rw null_iff at hr, simp [hr] },
    have hle := nat.add_le_add hle₀ hle₁,
    rw [← list.length_append, h] at hle, simpa using hle } }
| (node (some a) l r) := λ _, by {
  simp only [unsingleton, to_list],
  simp only [list.append_eq_nil, list.map_eq_nil],
  repeat { rw ← null_iff },
  split_ifs with hl hr; tauto }

/-- The number of key-value pairs. -/
def card : trie α → ℕ
| nil                 := 0
| (node none     l r) := l.card + r.card
| (node (some _) l r) := l.card + r.card + 1

theorem card_eq : ∀ (t : trie α),
  t.card = t.to_list.length
| nil                 := rfl
| (node none     l r) := by simp [card, to_list, l.card_eq, r.card_eq]
| (node (some _) l r) := by simp [card, to_list, l.card_eq, r.card_eq]

section lookup

/-- Look up the value at a key. -/
def lookup : pos_num → trie α → option α
| _                nil          := none
| pos_num.one      (node o _ _) := o
| (pos_num.bit0 k) (node _ l _) := l.lookup k
| (pos_num.bit1 k) (node _ _ r) := r.lookup k

theorem mem_lookup_iff : ∀ (k : pos_num) (a : α) (t : trie α),
  a ∈ t.lookup k ↔ sigma.mk k a ∈ to_list t
| k                _ nil          := by cases k; simp [lookup, to_list]
| pos_num.one      a (node o _ _) := by {
  cases o with a'; simp only [lookup, to_list],
  { simp },
  { suffices : a' = a ↔ a = a', by simpa, cc } }
| (pos_num.bit0 k) _ (node o l _) := by {
  cases o; simp only [lookup, to_list];
  rw mem_lookup_iff; simp }
| (pos_num.bit1 k) _ (node o _ r) := by {
  cases o; simp only [lookup, to_list];
  rw mem_lookup_iff; simp }

end lookup

section insert_with

/-- Insert a key-value pair. Return a new trie, using f(new_value, old_value) to resolve a
conflicted value if the key exists. -/
def insert_with (f : α → α → α) : pos_num → α → trie α → trie α
| pos_num.one      a nil                  := node (some a) nil nil
| pos_num.one      a (node none      l r) := node (some a) l r
| pos_num.one      a (node (some a') l r) := node (some (f a a')) l r
| (pos_num.bit0 k) a nil                  := node none (nil.insert_with k a) nil
| (pos_num.bit0 k) a (node o         l r) := node o (l.insert_with k a) r
| (pos_num.bit1 k) a nil                  := node none nil (nil.insert_with k a)
| (pos_num.bit1 k) a (node o         l r) := node o l (r.insert_with k a)

lemma mem_keys_append (ns₀ ns₁ : list (Σ _ : pos_num, α)) (k : pos_num) :
  k ∈ (ns₀ ++ ns₁).keys ↔ k ∈ ns₀.keys ∨ k ∈ ns₁.keys :=
by simp [list.keys]

lemma bit0_mem_map_bit0_keys (ns : list (Σ _ : pos_num, α)) (k : pos_num) :
  k.bit0 ∈ (map_bit0 ns).keys ↔ k ∈ ns.keys :=
by simp [list.keys]

lemma bit1_mem_map_bit1_keys (ns : list (Σ _ : pos_num, α)) (k : pos_num) :
  k.bit1 ∈ (map_bit1 ns).keys ↔ k ∈ ns.keys :=
by simp [list.keys]

lemma bit0_not_mem_map_bit1_keys (ns : list (Σ _ : pos_num, α)) (k : pos_num) :
  k.bit0 ∉ (map_bit1 ns).keys :=
by simp [list.keys]

lemma bit1_not_mem_map_bit0_keys (ns : list (Σ _ : pos_num, α)) (k : pos_num) :
  k.bit1 ∉ (map_bit0 ns).keys :=
by simp [list.keys]

theorem mem_insert_with_iff (f : α → α → α) : ∀ (k : pos_num) (a : α) (t : trie α) (s : (Σ _ : pos_num, α)),
  s ∈ (t.insert_with f k a).to_list ↔
  if s.1 = k then
    if k ∈ t.to_list.keys then
      ∃ (v : α), sigma.mk k v ∈ t.to_list ∧ s.2 = f a v
    else
      s.2 = a
  else
    s ∈ t.to_list
| pos_num.one      a nil                  := by simp [insert_with, to_list]
| pos_num.one      a (node none      l r) := λ ⟨_, _⟩, by {
  simp only [insert_with, to_list, list.mem_cons_iff],
  simp only [one_not_mem_keys_append_map_bit0_map_bit1, if_false],
  split_ifs with h; simp [h] }
| pos_num.one      a (node (some a') l r) := λ ⟨_, _⟩, by {
  simp only [insert_with, to_list],
  simp only [list.mem_cons_iff, list.keys_cons, eq_self_iff_true, true_and, true_or, if_true],
  split_ifs with h; simp [h] }
| (pos_num.bit0 k) a nil                  := λ s, by {
  suffices :
    (∃ k' a', (k' = k ∧ a' = a) ∧ (⟨k'.bit0, a'⟩ : (Σ _ : pos_num, α)) = s) ↔ s = ⟨k.bit0, a⟩,
  { cases s, simpa [insert_with, to_list, mem_insert_with_iff] },
  split,
  { rintro ⟨k', a', ⟨_, _⟩, _⟩, subst_vars },
  { tauto } }
| (pos_num.bit0 k) a (node o         l r) := λ s, by {
  suffices hiff :
    s ∈ map_bit0 (insert_with f k a l).to_list ++ map_bit1 r.to_list ↔
    if s.1 = k.bit0 then
      if k.bit0 ∈ (map_bit0 l.to_list ++ map_bit1 r.to_list).keys then
        ∃ v, (⟨k.bit0, v⟩ : (Σ _ : pos_num, α)) ∈ map_bit0 l.to_list ++ map_bit1 r.to_list ∧ s.2 = f a v
      else
        s.2 = a
    else
      s ∈ map_bit0 l.to_list ++ map_bit1 r.to_list,
  { cases o; simp only [insert_with, to_list],
    { apply hiff },
    { simp only [list.mem_cons_iff, list.keys_cons, false_or, false_and],
      by_cases h : s = ⟨pos_num.one, o⟩,
      { simp [h] },
      { simpa [h] using hiff } } },
  simp only [mem_keys_append, list.mem_append,
             bit0_mem_map_bit0_keys, bit0_not_mem_map_bit1_keys, or_false],
  conv in (s ∈ map_bit0 _) { simp only [list.mem_map] },
  simp only [mem_insert_with_iff],
  by_cases h : s.1 = k.bit0; simp only [h, eq_self_iff_true, if_true, if_false],
  { cases s, simp only at h, simp [h] },
  { apply or_congr_left,
    simp only [list.mem_map],
    split,
    { rintro ⟨s', h⟩,
      split_ifs at h with h₁ h₂,
      { exfalso, rcases h with ⟨_, _, _⟩, subst_vars, tauto },
      { exfalso, rcases h with ⟨_, _⟩, subst_vars, tauto },
      { existsi s', exact h } },
    { rintro ⟨s', _, _, _⟩, subst_vars, simp only at h,
      existsi s', simpa [h] } } }
| (pos_num.bit1 k) a nil                  := λ s, by {
  suffices :
    (∃ k' a', (k' = k ∧ a' = a) ∧ (⟨k'.bit1, a'⟩ : (Σ _ : pos_num, α)) = s) ↔ s = ⟨k.bit1, a⟩,
  { cases s, simpa [insert_with, to_list, mem_insert_with_iff] },
  split,
  { rintro ⟨k', a', ⟨_, _⟩, _⟩, subst_vars },
  { tauto } }
| (pos_num.bit1 k) a (node o         l r) := λ s, by {
  suffices hiff :
    s ∈ map_bit0 l.to_list ++ map_bit1 (insert_with f k a r).to_list ↔
    if s.1 = k.bit1 then
      if k.bit1 ∈ (map_bit0 l.to_list ++ map_bit1 r.to_list).keys then
        ∃ v, (⟨k.bit1, v⟩ : (Σ _ : pos_num, α)) ∈ map_bit0 l.to_list ++ map_bit1 r.to_list ∧ s.2 = f a v
      else
        s.2 = a
    else
      s ∈ map_bit0 l.to_list ++ map_bit1 r.to_list,
  { cases o; simp only [insert_with, to_list],
    { apply hiff },
    { simp only [list.mem_cons_iff, list.keys_cons, false_or, false_and],
      by_cases h : s = ⟨pos_num.one, o⟩,
      { simp [h] },
      { simpa [h] using hiff } } },
  simp only [mem_keys_append, list.mem_append,
             bit1_mem_map_bit1_keys, bit1_not_mem_map_bit0_keys, or_false],
  conv in (s ∈ map_bit1 _) { simp only [list.mem_map] },
  simp only [mem_insert_with_iff],
  by_cases h : s.1 = k.bit1; simp only [h, eq_self_iff_true, if_true, if_false],
  { cases s, simp only at h, simp [h] },
  { apply or_congr_right,
    simp only [list.mem_map],
    split,
    { rintro ⟨s', h⟩,
      split_ifs at h with h₁ h₂,
      { exfalso, rcases h with ⟨_, _, _⟩, subst_vars, tauto },
      { exfalso, rcases h with ⟨_, _⟩, subst_vars, tauto },
      { existsi s', exact h } },
    { rintro ⟨s', _, _, _⟩, subst_vars, simp only at h,
      existsi s', simpa [h] } } }

end insert_with

/-- Insert a key-value pair. Return a new trie if the key doesn't exist, otherwise return
the old trie. -/
def kinsert : pos_num → α → trie α → trie α :=
insert_with (λ new old, old)

theorem mem_kinsert_iff (k : pos_num) (a : α) (t : trie α) (s : (Σ _ : pos_num, α)) :
  s ∈ to_list (t.kinsert k a) ↔ s ∈ t.to_list ∨ (k ∉ t.to_list.keys ∧ s = ⟨k, a⟩) :=
begin
  simp only [kinsert],
  rw mem_insert_with_iff,
  split_ifs with h₁ h₂; subst_vars,
  { simp only [sigma.eta, exists_eq_right'],
    tauto },
  { split; intro h,
    { right, subst_vars, simp [h₂] },
    { cases s,
      rcases h with (_ | ⟨_, h₃⟩),
      { have := list.mem_keys_of_mem h, tauto },
      { subst_vars, simpa using h₃ } } },
   { suffices : k ∈ t.to_list.keys ∨ s ≠ ⟨k, a⟩, by tauto,
     right, cases s, simpa using h₁ }
end

/-- Insert a key-value pair. Return a new trie and `tt` if the key doesn't exist, otherwise
return the old trie and `ff`. -/
def kinsert' : pos_num → α → trie α → trie α × bool
| pos_num.one      a nil             := (node (some a) nil nil, tt)
| pos_num.one      a (node none l r) := (node (some a) l r, tt)
| pos_num.one      _ t               := (t, ff)
| (pos_num.bit0 k) a nil             := let p := nil.kinsert' k a in (node none p.1 nil, p.2)
| (pos_num.bit0 k) a (node o    l r) := let p := l.kinsert' k a in (node o p.1 r, p.2)
| (pos_num.bit1 k) a nil             := let p := nil.kinsert' k a in (node none nil p.1, p.2)
| (pos_num.bit1 k) a (node o    l r) := let p := r.kinsert' k a in (node o l p.1, p.2)

section update

/-- Desctructive update. Overrides any old value with associated key. -/
def update : pos_num → α → trie α → trie α :=
insert_with (λ new old, new)

theorem mem_update_iff (k : pos_num) (a : α) (t : trie α) (s : (Σ _ : pos_num, α)) :
  s ∈ to_list (t.update k a) ↔ if s.1 = k then s.2 = a else s ∈ t.to_list :=
begin
  simp only [update],
  rw mem_insert_with_iff,
  split_ifs with h₁ h₂; subst_vars,
  have := list.exists_of_mem_keys h₂,
  tauto
end

end update

/-! Smart constructors without using `decidable_eq` -/
section mk

/-- A smart constructor that simplifies `node none nil nil` to `nil`. -/
def mk : option α → trie α → trie α → trie α
| none nil nil := nil
| o    l   r   := node o l r

/-- A smart constructor that returns `nil` if left is `nil`. -/
def mk_if_l (o : option α) : trie α → trie α → trie α
| nil _ := nil
| l   r := node o l r

/-- A smart constructor that returns `nil` if right is `nil`. -/
def mk_if_r (o : option α) (l : trie α) : trie α → trie α
| nil := nil
| r   := node o l r

lemma mk_to_list : ∀ (o : option α) (l r : trie α),
  (mk o l r).to_list = (node o l r).to_list
| none     nil          nil          := by simp [mk, to_list]
| none     nil          (node _ _ _) := by simp [mk, to_list]
| none     (node _ _ _) _            := by simp [mk, to_list]
| (some _) l            r            := by simp [mk, to_list]

section
open classical
local attribute [instance] prop_decidable

lemma mk_if_l_eq (o : option α) : ∀ (l r : trie α),
  mk_if_l o l r = if l = nil then nil else node o l r
| nil          _ := by simp [mk_if_l]
| (node _ _ _) _ := by simp [mk_if_l]

lemma mk_if_r_eq (o : option α) (l : trie α) : ∀ (r : trie α),
  mk_if_r o l r = if r = nil then nil else node o l r
| nil          := by simp [mk_if_r]
| (node _ _ _) := by simp [mk_if_r]

end

end mk

section insert₂
variable [decidable_eq α]

/-- Insert a key-value pair. Return `nil` if the key already exists in the trie and is associated
with a different value. -/
def insert₂ : pos_num → α → trie α → trie α
| pos_num.one      a nil                  := node (some a) nil nil
| pos_num.one      a (node none      l r) := node (some a) l r
| pos_num.one      a (node (some a') l r) := if a = a' then node (some a') l r else nil
| (pos_num.bit0 k) a nil                  := node none (nil.insert₂ k a) nil
| (pos_num.bit0 k) a (node o         l r) := mk_if_l o (l.insert₂ k a) r
| (pos_num.bit1 k) a nil                  := node none nil (nil.insert₂ k a)
| (pos_num.bit1 k) a (node o         l r) := mk_if_r o l (r.insert₂ k a)

/-- Justify that it's okay for `insert₂` to check against `nil` instead of using `null`. -/
theorem insert₂_eq_nil_iff : ∀ (k : pos_num) (a : α) (t : trie α),
  t.insert₂ k a = nil ↔ (t.insert₂ k a).to_list = []
| pos_num.one      a nil                  := by simp [insert₂, to_list]
| pos_num.one      a (node none      l r) := by simp [insert₂, to_list]
| pos_num.one      a (node (some a') l r) := by {
  simp only [insert₂],
  split_ifs with h; simp [to_list] }
| (pos_num.bit0 k) a nil                  := by {
  suffices : ¬ (insert₂ k a nil).to_list = [],
  by simpa [insert₂, to_list],
  rw ← insert₂_eq_nil_iff, cases k; simp [insert₂] }
| (pos_num.bit0 k) a (node o         l r) := by {
  simp only [insert₂, mk_if_l_eq],
  split_ifs with h,
  { simp [to_list] },
  { cases o,
    { rw insert₂_eq_nil_iff at h, simp [to_list, h] },
    { simp [to_list] } } }
| (pos_num.bit1 k) a nil                  := by {
  suffices : ¬ (insert₂ k a nil).to_list = [],
  by simpa [insert₂, to_list],
  rw ← insert₂_eq_nil_iff, cases k; simp [insert₂] }
| (pos_num.bit1 k) a (node o         l r) := by {
  simp only [insert₂, mk_if_r_eq],
  split_ifs with h,
  { simp [to_list] },
  { cases o,
    { rw insert₂_eq_nil_iff at h, simp [to_list, h] },
    { simp [to_list] } } }

theorem insert₂_ne_nil_iff : ∀ (k : pos_num) (a : α) (t : trie α),
  t.insert₂ k a ≠ nil ↔ (k ∈ t.to_list.keys → sigma.mk k a ∈ t.to_list)
| pos_num.one      a nil                  := by simp [insert₂, to_list]
| pos_num.one      a (node none      l r) := by simp [insert₂, to_list, list.keys]
| pos_num.one      a (node (some a') l r) := by simp [insert₂, to_list]
| (pos_num.bit0 k) a nil                  := by simp [insert₂, to_list]
| (pos_num.bit0 k) a (node o         l r) := by {
  suffices : insert₂ k a l ≠ nil ↔
             k.bit0 ∈ (map_bit0 l.to_list ++ map_bit1 r.to_list).keys → sigma.mk k a ∈ l.to_list,
  { cases o; simpa [insert₂, to_list, mk_if_l_eq] },
  rw insert₂_ne_nil_iff, simp [list.keys] }
| (pos_num.bit1 k) a nil                 := by simp [insert₂, to_list]
| (pos_num.bit1 k) a (node o        l r) := by {
  suffices : insert₂ k a r ≠ nil ↔
             k.bit1 ∈ (map_bit0 l.to_list ++ map_bit1 r.to_list).keys → sigma.mk k a ∈ r.to_list,
  { cases o; simpa [insert₂, to_list, mk_if_r_eq] },
  rw insert₂_ne_nil_iff, simp [list.keys] }

theorem mem_insert₂_iff : ∀ (k : pos_num) (a : α) (t : trie α) (s : (Σ _ : pos_num, α)),
  s ∈ (t.insert₂ k a).to_list ↔
  (s = ⟨k, a⟩ ∨ s ∈ t.to_list) ∧ (k ∈ t.to_list.keys → sigma.mk k a ∈ t.to_list)
| pos_num.one      a nil                  := by simp [insert₂, to_list]
| pos_num.one      a (node none      l r) := by simp [insert₂, to_list, list.keys]
| pos_num.one      a (node (some a') l r) := λ _, by {
  simp only [insert₂],
  split_ifs with h; simp [h, to_list] }
| (pos_num.bit0 k) a nil                  := λ s, by {
  suffices : (∃ s', s' = sigma.mk k a ∧ (⟨s'.1.bit0, s'.2⟩ : Σ _ : pos_num, α) = s) ↔
             s = ⟨k.bit0, a⟩, by simpa [insert₂, mem_insert₂_iff, to_list],
  split,
  { rintro ⟨s', h₁, h₂⟩, subst_vars },
  { tauto } }
| (pos_num.bit0 k) a (node o        l r) := λ s, by {
  simp only [insert₂, mk_if_l_eq],
  split_ifs with hl,
  { -- insert₂ k a l = ∅
    simp only [to_list, list.not_mem_nil, false_iff, not_and],
    intro hs, clear hs,
    suffices : (∃ (a' : α), sigma.mk k a' ∈ l.to_list) ∧ sigma.mk k a ∉ l.to_list,
    { cases o; simpa [to_list, list.mem_keys] },
    have h : sigma.mk k a ∈ (insert₂ k a l).to_list ↔ sigma.mk k a ∈ nil.to_list,
    { rw hl },
    have h : k ∈ l.to_list.keys ∧ sigma.mk k a ∉ l.to_list,
    { simpa [mem_insert₂_iff, to_list] using h },
    simpa [list.mem_keys] using h },
  { -- insert₂ k a l ≠ ∅
    rw [← ne.def, insert₂_ne_nil_iff] at hl,

    -- Prove `himp` and remove it from goal.
    have himp : k.bit0 ∈ (node o l r).to_list.keys →
                (⟨k.bit0, a⟩ : Σ _ : pos_num, α) ∈ (node o l r).to_list,
    { cases o;
      simpa [to_list, mem_keys_append, bit0_mem_map_bit0_keys, bit0_not_mem_map_bit1_keys] },
    suffices : s ∈ (node o (insert₂ k a l) r).to_list ↔
               (s = ⟨k.bit0, a⟩ ∨ s ∈ (node o l r).to_list),
    { split; intro h,
      { split, { tauto }, { exact himp } },
      { tauto } },
    clear himp,

    have hiff : s ∈ map_bit0 (insert₂ k a l).to_list ++ map_bit1 r.to_list ↔
                (s = ⟨k.bit0, a⟩ ∨ s ∈ map_bit0 l.to_list ++ map_bit1 r.to_list),
    { simp only [list.mem_append],
      rw ← or_assoc, apply or_congr_left,
      simp only [list.mem_map, mem_insert₂_iff],
      split,
      { rintro ⟨s', ⟨⟨h₁ | h₁, h₂⟩, h₃⟩⟩,
        { left, subst_vars },
        { right, subst_vars, simp [h₁] } },
      { rintro (h | ⟨s', h₁, h₂⟩),
        { existsi sigma.mk k a, tauto },
        { existsi s', tauto } } },

    cases o with a'; simp only [to_list],
    { rw hiff },
    { simp only [list.mem_cons_iff],
      rw hiff, tauto } } }
| (pos_num.bit1 k) a nil                  := λ s, by {
  suffices : (∃ s', s' = sigma.mk k a ∧ (⟨s'.1.bit1, s'.2⟩ : Σ _ : pos_num, α) = s) ↔
             s = ⟨k.bit1, a⟩, by simpa [insert₂, mem_insert₂_iff, to_list],
  split,
  { rintro ⟨s', h₁, h₂⟩, subst_vars },
  { tauto } }
| (pos_num.bit1 k) a (node o         l r) := λ s, by {
  simp only [insert₂, mk_if_r_eq],
  split_ifs with hr,
  { -- insert₂ k a r = ∅
    simp only [to_list, list.not_mem_nil, false_iff, not_and],
    intro hs, clear hs,
    suffices : (∃ (a' : α), sigma.mk k a' ∈ r.to_list) ∧ sigma.mk k a ∉ r.to_list,
    { cases o; simpa [to_list, list.mem_keys] },
    have h : sigma.mk k a ∈ (insert₂ k a r).to_list ↔ sigma.mk k a ∈ nil.to_list,
    { rw hr },
    have h : k ∈ r.to_list.keys ∧ sigma.mk k a ∉ r.to_list,
    { simpa [mem_insert₂_iff, to_list] using h },
    simpa [list.mem_keys] using h },
  { -- insert₂ k a r ≠ ∅
    rw [← ne.def, insert₂_ne_nil_iff] at hr,

    -- Prove `himp` and remove it from goal.
    have himp : k.bit1 ∈ (node o l r).to_list.keys →
                (⟨k.bit1, a⟩ : Σ _ : pos_num, α) ∈ (node o l r).to_list,
    { cases o;
      simpa [to_list, mem_keys_append, bit1_mem_map_bit1_keys, bit1_not_mem_map_bit0_keys] },
    suffices : s ∈ (node o l (insert₂ k a r)).to_list ↔
               (s = ⟨k.bit1, a⟩ ∨ s ∈ (node o l r).to_list),
    { split; intro h,
      { split, { tauto }, { exact himp } },
      { tauto } },
    clear himp,

    have hiff : s ∈ map_bit0 l.to_list ++ map_bit1 (insert₂ k a r).to_list ↔
                (s = ⟨k.bit1, a⟩ ∨ s ∈ map_bit0 l.to_list ++ map_bit1 r.to_list),
    { simp only [list.mem_append],
      rw or.left_comm, apply or_congr_right,
      simp only [list.mem_map, mem_insert₂_iff],
      split,
      { rintro ⟨s', ⟨⟨h₁ | h₁, h₂⟩, h₃⟩⟩,
        { left, subst_vars },
        { right, subst_vars, simp [h₁] } },
      { rintro (h | ⟨s', h₁, h₂⟩),
        { existsi sigma.mk k a, tauto },
        { existsi s', tauto } } },

    cases o with a'; simp only [to_list],
    { rw hiff },
    { simp only [list.mem_cons_iff],
      rw hiff, tauto } } }

end insert₂

/-- Erase a key and its value. -/
def kerase : trie α → pos_num → trie α
| nil          _                := nil
| (node _ l r) pos_num.one      := mk none l r
| (node o l r) (pos_num.bit0 k) := mk o (l.kerase k) r
| (node o l r) (pos_num.bit1 k) := mk o l (r.kerase k)

theorem mem_kerase_iff : ∀ (t : trie α) (k : pos_num) (s : (Σ _ : pos_num, α)),
  s ∈ (t.kerase k).to_list ↔ s.1 ≠ k ∧ s ∈ t.to_list
| nil          _                := by simp [kerase, to_list]
| (node o l r) pos_num.one      := λ s, by {
    have hiff : s ∈ map_bit0 l.to_list ++ map_bit1 r.to_list ↔
                s.fst ≠ pos_num.one ∧ s ∈ map_bit0 l.to_list ++ map_bit1 r.to_list,
    { symmetry, rw and_iff_right_iff_imp,
      have h := one_not_mem_keys_append_map_bit0_map_bit1 l.to_list r.to_list,
      rw list.not_eq_key at h, tauto },
    cases o with a; simp only [kerase, to_list, mk_to_list],
    { exact hiff },
    { rw [list.mem_cons_iff, and_or_distrib_left],
      have hfalse : ¬ (s.fst ≠ pos_num.one ∧ s = ⟨pos_num.one, a⟩),
      { cases s, simp only [not_and], tauto },
      simpa only [hfalse, false_or] } }
| (node o l r) (pos_num.bit0 k) := λ s, by {
    have hiff : s ∈ map_bit0 (l.kerase k).to_list ∨ s ∈ map_bit1 r.to_list ↔
                s.fst ≠ k.bit0 ∧ (s ∈ map_bit0 l.to_list ∨ s ∈ map_bit1 r.to_list),
    { simp only [list.mem_map, mem_kerase_iff],
      split,
      { rintro (⟨s', ⟨h₁, h₂⟩, h₃⟩ | ⟨s', h₁, h₂⟩),
        { subst_vars, simp [h₁, h₂] },
        { subst_vars, simp [h₁] } },
      { rintro ⟨h, ⟨s', h₁, h₂⟩ | ⟨s', h₁, h₂⟩⟩,
        { left, existsi s', subst_vars, tauto },
        { right, existsi s', subst_vars, tauto } } },
   cases o with a'; simp only [kerase, to_list, mk_to_list, list.mem_append, list.mem_cons_iff],
   { rw hiff },
   { split,
     { rintro (h | h),
       { split, { subst h, simp }, { tauto } },
       { rw hiff at h, tauto } },
     { rintro ⟨h₁, h₂ | h₂⟩,
       { tauto },
       { right, rw hiff, tauto } } } }
| (node o l r) (pos_num.bit1 k) := λ s, by {
    have hiff : s ∈ map_bit0 l.to_list ∨ s ∈ map_bit1 (r.kerase k).to_list ↔
                s.fst ≠ k.bit1 ∧ (s ∈ map_bit0 l.to_list ∨ s ∈ map_bit1 r.to_list),
    { simp only [list.mem_map, mem_kerase_iff],
      split,
      { rintro (⟨s', h₁, h₂⟩ | ⟨s', ⟨h₁, h₂⟩, h₃⟩),
        { subst_vars, simp [h₁] },
        { subst_vars, simp [h₁, h₂] } },
      { rintro ⟨h, ⟨s', h₁, h₂⟩ | ⟨s', h₁, h₂⟩⟩,
        { left, existsi s', subst_vars, tauto },
        { right, existsi s', subst_vars, tauto } } },
   cases o with a'; simp only [kerase, to_list, mk_to_list, list.mem_append, list.mem_cons_iff],
   { rw hiff },
   { split,
     { rintro (h | h),
       { split, { subst h, simp }, { tauto } },
       { rw hiff at h, tauto } },
     { rintro ⟨h₁, h₂ | h₂⟩,
       { tauto },
       { right, rw hiff, tauto } } } }

section erase₂
variable [decidable_eq α]

/-- Erase a key and its value. -/
def erase₂ : trie α → pos_num → α → trie α
| nil                  _                := λ _, nil
| (node none      l r) pos_num.one      := λ _, node none l r
| (node (some a') l r) pos_num.one      := λ a, if a = a' then mk none l r else node (some a') l r
| (node o         l r) (pos_num.bit0 k) := λ a, mk o (l.erase₂ k a) r
| (node o         l r) (pos_num.bit1 k) := λ a, mk o l (r.erase₂ k a)

theorem mem_erase₂_iff : ∀ (t : trie α) (k : pos_num) (a : α) (s : (Σ _ : pos_num, α)),
  s ∈ (t.erase₂ k a).to_list ↔ s ≠ ⟨k, a⟩ ∧ s ∈ t.to_list
| nil                  _                := by simp [erase₂, to_list]
| (node none      l r) pos_num.one      := λ a s, by {
  simp only [erase₂, to_list, list.mem_append],
  split,
  { intro h, split,
    { contrapose! h, cases h, simp },
    { exact h } },
  { rintro ⟨_, h⟩, exact h } }
| (node (some a') l r) pos_num.one      := λ a s, by {
  simp only [erase₂],
  cases decidable.em (a = a') with hcmp hcmp;
  simp only [hcmp, eq_self_iff_true, if_true, if_false, mk_to_list, to_list,
             list.mem_append, list.mem_cons_iff];
  { split,
    { intro h, split,
      { contrapose! h, cases h, simp [hcmp] },
      { tauto } },
    { rintro ⟨_, (h | h)⟩; tauto } } }
| (node o         l r) (pos_num.bit0 k) := λ a s, by {
  have hiff : s ∈ map_bit0 (l.erase₂ k a).to_list ∨ s ∈ map_bit1 r.to_list ↔
              s ≠ ⟨k.bit0, a⟩ ∧ (s ∈ map_bit0 l.to_list ∨ s ∈ map_bit1 r.to_list),
  { nth_rewrite_lhs 0 [list.mem_map],
    nth_rewrite_rhs 0 [list.mem_map],
    simp only [mem_erase₂_iff],
    split,
    { rintro (⟨s', ⟨h₁, h₂⟩, h₃⟩ | h),
      { cases h₃, split,
        { contrapose! h₁, cases h₁, subst_vars, simp },
        { left, existsi s', exact and.intro h₂ h₃ } },
      { split,
        { contrapose! h, cases h, simp },
        { right, exact h } } },
    { rintro ⟨h₁, ⟨s', h₂, h₃⟩ | h₂⟩,
      { left, cases h₃, existsi s', split,
        { split,
          { contrapose! h₁, cases h₁, simp },
          { exact h₂ } },
        { exact h₃ } },
      { right, exact h₂ } } },

  cases o with a'; simp only [erase₂, mk_to_list, to_list, list.mem_append, list.mem_cons_iff],
  { rw hiff },
  { rw hiff,
    split,
    { rintro (h | ⟨h₁, h₂⟩),
      { cases h, simp },
      { split,
        { exact h₁ },
        { right, exact h₂ } } },
    { rintro ⟨h₁, h₂ | h₂⟩,
      { left, exact h₂ },
      { right, exact and.intro h₁ h₂ } } } }
| (node o         l r) (pos_num.bit1 k) := λ a s, by {
  have hiff : s ∈ map_bit0 l.to_list ∨ s ∈ map_bit1 (r.erase₂ k a).to_list ↔
              s ≠ ⟨k.bit1, a⟩ ∧ (s ∈ map_bit0 l.to_list ∨ s ∈ map_bit1 r.to_list),
  { nth_rewrite_lhs 1 [list.mem_map],
    nth_rewrite_rhs 1 [list.mem_map],
    simp only [mem_erase₂_iff],
    split,
    { rintro (h | ⟨s', ⟨h₁, h₂⟩, h₃⟩),
      { split,
        { contrapose! h, cases h, simp },
        { left, exact h } },
      { cases h₃, split,
        { contrapose! h₁, cases h₁, subst_vars, simp },
        { right, existsi s', exact and.intro h₂ h₃ } } },
    { rintro ⟨h₁, h₂ | ⟨s', h₂, h₃⟩⟩,
      { left, exact h₂ },
      { right, cases h₃, existsi s', split,
        { split,
          { contrapose! h₁, cases h₁, simp },
          { exact h₂ } },
        { exact h₃ } } } },

  cases o with a'; simp only [erase₂, mk_to_list, to_list, list.mem_append, list.mem_cons_iff],
  { rw hiff },
  { rw hiff,
    split,
    { rintro (h | ⟨h₁, h₂⟩),
      { cases h, simp },
      { split,
        { exact h₁ },
        { right, exact h₂ } } },
    { rintro ⟨h₁, h₂ | h₂⟩,
      { left, exact h₂ },
      { right, exact and.intro h₁ h₂ } } } }

end erase₂

section ksdiff
variable {β : Type*}

/-- Remove key-values pairs from one trie whose keys are also in another trie. -/
def ksdiff : trie α → trie β → trie α
| t₁                     nil                   := t₁
| nil                    _                     := nil
| (node o₁        l₁ r₁) (node none     l₂ r₂) := mk o₁ (l₁.ksdiff l₂) (r₁.ksdiff r₂)
| (node _         l₁ r₁) (node (some _) l₂ r₂) := mk none (l₁.ksdiff l₂) (r₁.ksdiff r₂)

theorem mem_ksdiff_iff : ∀ (t₁ : trie α) (t₂ : trie β) (s : (Σ _ : pos_num, α)),
  s ∈ (t₁.ksdiff t₂).to_list ↔ (s ∈ t₁.to_list ∧ s.1 ∉ t₂.to_list.keys)
| nil             nil                   := by simp [ksdiff, to_list]
| nil             (node _        _  _)  := by simp [ksdiff, to_list]
| (node _  _  _)  nil                   := by simp [ksdiff, to_list]
| (node o₁ l₁ r₁) (node none     l₂ r₂) := λ s, by {
  suffices : s ∈ map_bit0 (l₁.ksdiff l₂).to_list ++ map_bit1 (r₁.ksdiff r₂).to_list ↔
             s ∈ map_bit0 l₁.to_list ++ map_bit1 r₁.to_list ∧
             s.fst ∉ (map_bit0 l₂.to_list ++ map_bit1 r₂.to_list).keys,
  { cases o₁ with a; simp only [ksdiff, to_list, mk_to_list, list.mem_cons_iff],
    { assumption },
    { split,
      { rintro (h | h),
        { subst_vars, split,
          { left, refl },
          { apply one_not_mem_keys_append_map_bit0_map_bit1 } },
        { rw this at h, tauto } },
      { rintro ⟨h₁ | h₁, h₂⟩,
        { left, exact h₁ },
        { right, rw this, tauto } } } },
  simp only [list.mem_append, mem_keys_append],
  simp only [list.mem_map, list.keys, mem_ksdiff_iff],
  simp only [not_exists, not_and, not_or_distrib, exists_imp_distrib, and_imp],
  split,
  { rintro (⟨s₁, ⟨⟨h₁, h₂⟩, h₃⟩⟩ | ⟨s₁, ⟨⟨h₁, h₂⟩, h₃⟩⟩);
    subst_vars; simp only [sigma.eta, heq_iff_eq],
    { split,
      { left, existsi s₁, tauto },
      { split; intros; subst_vars; simp only [sigma.eta]; tauto } },
    { split,
      { right, existsi s₁, tauto },
      { split; intros; subst_vars; simp only [sigma.eta]; tauto } } },
  { rintro ⟨⟨s', h₁, h₂⟩ | ⟨s', h₁, h₂⟩, ⟨h₃, h₄⟩⟩;
    subst_vars; simp only [sigma.eta] at h₃ h₄,
    { left, existsi s',
      split; try { cc },
      split; try { assumption },
      intros x hx, simpa using h₃ ⟨x.1.bit0, x.2⟩ _ hx },
    { right, existsi s',
      split; try { cc },
      split; try { assumption },
      intros x hx, simpa using h₄ ⟨x.1.bit1, x.2⟩ _ hx } } }
| (node o₁ l₁ r₁) (node (some _) l₂ r₂) := λ s, by {
  suffices : s ∈ map_bit0 (l₁.ksdiff l₂).to_list ++ map_bit1 (r₁.ksdiff r₂).to_list ↔
             s ∈ map_bit0 l₁.to_list ++ map_bit1 r₁.to_list ∧ ¬s.fst = pos_num.one ∧
             s.fst ∉ (map_bit0 l₂.to_list ++ map_bit1 r₂.to_list).keys,
  { cases o₁ with a;
    simp only [ksdiff, to_list, mk_to_list, list.mem_cons_iff, list.keys_cons, not_or_distrib],
    { assumption },
    { split,
      { rw this, tauto },
      { rintro ⟨h₁ | h₁, ⟨h₂, h₃⟩⟩,
        { cc },
        { rw this, tauto } } } },
  simp only [list.mem_append, mem_keys_append],
  simp only [list.mem_map, list.keys, mem_ksdiff_iff],
  simp only [not_exists, not_and, not_or_distrib, exists_imp_distrib, and_imp],
  split,
  { rintro (⟨s₁, ⟨h₁, h₂⟩⟩ | ⟨s₁, ⟨h₁, h₂⟩⟩);
    subst_vars; simp only [sigma.eta, heq_iff_eq, not_false_iff, true_and],
    { split,
      { left, existsi s₁, tauto },
      { split; intros; subst_vars; simp only [sigma.eta]; tauto } },
    { split,
      { right, existsi s₁, tauto },
      { split; intros; subst_vars; simp only [sigma.eta]; tauto } } },
  { rintro ⟨⟨s', h₁, h₂⟩ | ⟨s', h₁, h₂⟩, ⟨h₃, ⟨h₄, h₅⟩⟩⟩;
    subst_vars; simp only [sigma.eta] at h₃ h₄ h₅,
    { left, existsi s',
      split; try { cc },
      split; try { assumption },
      intros x hx, simpa using h₄ ⟨x.1.bit0, x.2⟩ _ hx },
    { right, existsi s',
      split; try { cc },
      split; try { assumption },
      intros x hx, simpa using h₅ ⟨x.1.bit1, x.2⟩ _ hx } } }

end ksdiff

section union₂
variable [decidable_eq α]

/-- Merge key-value pairs from two tries. Return `nil` if there are conflicting key-value pairs.

Unlike `insert₂`, merging two tries cannot use `nil` alone to indicate conflicts, since both tries
might be empty or have empty subtries. This helper function uses `option` to distinguish conflicts
from empty tries. -/
def union₂ : trie α → trie α → option (trie α)
| t                      nil                    := some t
| nil                    t                      := some t
| (node o₁        l₁ r₁) (node none      l₂ r₂) := do
  l ← l₁.union₂ l₂,
  r ← r₁.union₂ r₂,
  some $ node o₁ l r
| (node none      l₁ r₁) (node o₂        l₂ r₂) := do
  l ← l₁.union₂ l₂,
  r ← r₁.union₂ r₂,
  some $ node o₂ l r
| (node (some a₁) l₁ r₁) (node (some a₂) l₂ r₂) :=
  if a₁ = a₂ then do
    l ← l₁.union₂ l₂,
    r ← r₁.union₂ r₂,
    some $ node (some a₁) l r
  else
    none

theorem union₂_comm : ∀ (t₁ t₂ : trie α),
  union₂ t₁ t₂ = union₂ t₂ t₁
| nil             nil             := by refl
| (node o₁ l₁ r₁) nil             := by cases o₁; refl
| nil             (node o₂ l₂ r₂) := by cases o₂; refl
| (node o₁ l₁ r₁) (node o₂ l₂ r₂) := by {
  cases o₁; cases o₂;
  simp only [union₂]; rw [union₂_comm l₁ l₂, union₂_comm r₁ r₂];
  split_ifs; subst_vars; tauto }

theorem mem_or_mem_of_union₂ : ∀ {t₁ t₂ t : trie α} {s : (Σ _ : pos_num, α)},
  t₁.union₂ t₂ = some t →
  s ∈ t.to_list →
  s ∈ t₁.to_list ∨ s ∈ t₂.to_list
| nil                    nil                    := λ t s h, by {
  simp only [union₂] at h, subst h, simp }
| (node o₁        l₁ r₁) nil                    := λ t s h, by {
  cases o₁; {
    simp only [union₂] at h, subst h,
    intro, left, assumption } }
| nil                    (node o₂        l₂ r₂) := λ t s h, by {
  cases o₂; {
    simp only [union₂] at h, subst h,
    intro, right, assumption } }
| (node none      l₁ r₁) (node none      l₂ r₂) := λ t s h, by {
  simp only [union₂, option.bind_eq_some] at h,
  rcases h with ⟨l, ⟨hl, r, ⟨hr, ht⟩⟩⟩, subst ht,
  simp only [to_list, list.mem_append, list.mem_map],
  rintro (h | h); rcases h with ⟨s', h₁, h₂⟩; cases h₂,
  { simp [mem_or_mem_of_union₂ hl h₁] },
  { simp [mem_or_mem_of_union₂ hr h₁] } }
| (node (some a₁) l₁ r₁) (node none      l₂ r₂) := λ t s h, by {
  simp only [union₂, option.bind_eq_some] at h,
  rcases h with ⟨l, ⟨hl, r, ⟨hr, ht⟩⟩⟩, subst ht,
  simp only [to_list, list.mem_append, list.mem_cons_iff, list.mem_map],
  rintro (h | h), { left, left, exact h },
  cases h; rcases h with ⟨s', h₁, h₂⟩; cases h₂,
  { simp [mem_or_mem_of_union₂ hl h₁] },
  { simp [mem_or_mem_of_union₂ hr h₁] } }
| (node none      l₁ r₁) (node (some a₂) l₂ r₂) := λ t s h, by {
  simp only [union₂, option.bind_eq_some] at h,
  rcases h with ⟨l, ⟨hl, r, ⟨hr, ht⟩⟩⟩, subst ht,
  simp only [to_list, list.mem_append, list.mem_cons_iff, list.mem_map],
  rintro (h | h), { right, left, exact h },
  cases h; rcases h with ⟨s', h₁, h₂⟩; cases h₂,
  { simp [mem_or_mem_of_union₂ hl h₁] },
  { simp [mem_or_mem_of_union₂ hr h₁] } }
| (node (some a₁) l₁ r₁) (node (some a₂) l₂ r₂) := λ t s h, by {
  simp only [union₂] at h,
  split_ifs at h, swap, { exfalso, assumption },
  simp only [option.bind_eq_some] at h,
  rcases h with ⟨l, ⟨hl, r, ⟨hr, ht⟩⟩⟩, subst_vars,
  simp only [to_list, list.mem_append, list.mem_cons_iff, list.mem_map],
  rintro (h | h), { left, left, exact h },
  cases h; rcases h with ⟨s', h₁, h₂⟩; cases h₂,
  { simp [mem_or_mem_of_union₂ hl h₁] },
  { simp [mem_or_mem_of_union₂ hr h₁] } }

theorem subset_of_union₂_left : ∀ {t₁ t₂ t : trie α},
  t₁.union₂ t₂ = some t →
  t₁.to_list ⊆ t.to_list
| nil                    nil                    := by simp [union₂]
| (node o₁ l₁ r₁)        nil                    := by cases o₁; simp [union₂]
| nil                    (node o₂ l₂ r₂)        := by cases o₂; simp [to_list]
| (node none      l₁ r₁) (node o         l₂ r₂) := λ t h, by {
  cases o with a₂; {
    simp only [union₂, ne.def, option.bind_eq_none, not_forall, not_not] at h,
    simp only [option.mem_def, option.bind_eq_some] at h,
    rcases h with ⟨l, hl, r, hr, ht⟩, subst_vars,
    intro s,
    simp only [to_list, list.mem_append, list.mem_cons_iff, list.mem_map],
    rintro (h₁ | h₁); rcases h₁ with ⟨s', h₁, h₂⟩; subst_vars,
    { suffices : s' ∈ l.to_list, by simpa,
      tauto },
    { suffices : s' ∈ r.to_list, by simpa,
      tauto } } }
| (node (some a₁) l₁ r₁) (node none      l₂ r₂) := λ t h, by {
  simp only [union₂, ne.def, option.bind_eq_none, not_forall, not_not] at h,
  simp only [option.mem_def, option.bind_eq_some] at h,
  rcases h with ⟨l, hl, r, hr, ht⟩, subst_vars,
  intro s,
  simp only [to_list, list.mem_append, list.mem_cons_iff, list.mem_map],
  rintro (h₁ | h₁), { left, exact h₁ },
  rcases h₁ with (h₁ | h₁); rcases h₁ with ⟨s', h₁, h₂⟩; subst_vars,
  { suffices : s' ∈ l.to_list, by simpa,
    tauto },
  { suffices : s' ∈ r.to_list, by simpa,
    tauto } }
| (node (some a₁) l₁ r₁) (node (some a₂) l₂ r₂) := λ t h, by {
  simp only [union₂] at h,
  split_ifs at h with heq, swap, { exfalso, exact h },
  simp only [option.bind_eq_some] at h,
  rcases h with ⟨l, hl, r, hr, ht⟩, subst_vars,
  intro s,
  simp only [to_list, list.mem_append, list.mem_cons_iff, list.mem_map],
  rintro (h₁ | h₁), { left, exact h₁ },
  rcases h₁ with (h₁ | h₁); rcases h₁ with ⟨s', h₁, h₂⟩; subst_vars,
  { suffices : s' ∈ l.to_list, by simpa,
    tauto },
  { suffices : s' ∈ r.to_list, by simpa,
    tauto } }

theorem subset_of_union₂_right {t₁ t₂ t : trie α} :
  t₁.union₂ t₂ = some t →
  t₂.to_list ⊆ t.to_list :=
begin
  rw [union₂_comm],
  apply subset_of_union₂_left
end

theorem eq_of_union₂_ne_none : ∀ {t₁ t₂ : trie α},
  t₁.union₂ t₂ ≠ none →
  ∀ {k : pos_num} {a₁ a₂ : α},
    sigma.mk k a₁ ∈ t₁.to_list →
    sigma.mk k a₂ ∈ t₂.to_list →
    a₁ = a₂
| nil                    nil                    := by simp [to_list]
| (node o₁        l₁ r₁) nil                    := by cases o₁; simp [to_list]
| nil                    (node o₂        l₂ r₂) := by cases o₂; simp [to_list]
| (node none      l₁ r₁) (node none      l₂ r₂) := λ h k _ _ h₁ h₂, by {
  simp only [union₂, ne.def, option.bind_eq_none, not_forall, not_not] at h,
  simp only [option.mem_def, option.bind_eq_some] at h,
  rcases h with ⟨t, l, hl, r, hr, ht⟩, subst_vars,
  rw [option.mem_def] at hl,
  simp only [to_list, list.mem_append, list.mem_map] at h₁ h₂,
  cases h₁; rcases h₁ with ⟨⟨k₁, a₁'⟩, h₃, h₄, _⟩;
  cases h₂; rcases h₂ with ⟨⟨k₂, a₂'⟩, h₅, h₆, _⟩; subst_vars;
  simp only at h₆ ⊢; subst_vars;
  { apply eq_of_union₂_ne_none _ h₃ h₅, simp [hl, hr] } <|>
  { exfalso, assumption } }
| (node (some a₁) l₁ r₁) (node none      l₂ r₂) := λ h k _ _ h₁ h₂, by {
  simp only [union₂, ne.def, option.bind_eq_none, not_forall, not_not] at h,
  simp only [option.mem_def, option.bind_eq_some] at h,
  rcases h with ⟨t, l, hl, r, hr, ht⟩, subst_vars,
  rw [option.mem_def] at hl,
  simp only [to_list, list.mem_append, list.mem_cons_iff, list.mem_map] at h₁ h₂,
  rcases h₁ with (⟨_, _⟩ | h₁), { subst_vars, exfalso, simpa using h₂ },
  cases h₁; rcases h₁ with ⟨⟨k₁, a₁'⟩, h₃, h₄, _⟩;
  cases h₂; rcases h₂ with ⟨⟨k₂, a₂'⟩, h₅, h₆, _⟩; subst_vars;
  simp only at h₆ ⊢; subst_vars;
  { apply eq_of_union₂_ne_none _ h₃ h₅, simp [hl, hr] } <|>
  { exfalso, assumption } }
| (node none      l₁ r₁) (node (some a₂) l₂ r₂) := λ h k _ _ h₁ h₂, by {
  simp only [union₂, ne.def, option.bind_eq_none, not_forall, not_not] at h,
  simp only [option.mem_def, option.bind_eq_some] at h,
  rcases h with ⟨t, l, hl, r, hr, ht⟩, subst_vars,
  rw [option.mem_def] at hl,
  simp only [to_list, list.mem_append, list.mem_cons_iff, list.mem_map] at h₁ h₂,
  rcases h₂ with (⟨_, _⟩ | h₂), { subst_vars, exfalso, simpa using h₁ },
  cases h₁; rcases h₁ with ⟨⟨k₁, a₁'⟩, h₃, h₄, _⟩;
  cases h₂; rcases h₂ with ⟨⟨k₂, a₂'⟩, h₅, h₆, _⟩; subst_vars;
  simp only at h₆ ⊢; subst_vars;
  { apply eq_of_union₂_ne_none _ h₃ h₅, simp [hl, hr] } <|>
  { exfalso, assumption } }
| (node (some a₁) l₁ r₁) (node (some a₂) l₂ r₂) := λ h k _ _ h₁ h₂, by {
  simp only [union₂] at h,
  split_ifs at h, swap, { exfalso, simpa using h },
  simp only [union₂, ne.def, option.bind_eq_none, not_forall, not_not] at h,
  simp only [option.mem_def, option.bind_eq_some] at h,
  rcases h with ⟨t, l, hl, r, hr, ht⟩, subst_vars,
  rw [option.mem_def] at hl,
  simp only [to_list, list.mem_append, list.mem_cons_iff, list.mem_map] at h₁ h₂,
  rcases h₁ with (⟨_, _⟩ | h₁), { subst_vars, symmetry, simp at h₂, simpa using h₂ },
  rcases h₂ with (⟨_, _⟩ | h₂), { subst_vars, simpa using h₁ },
  cases h₁; rcases h₁ with ⟨⟨k₁, a₁'⟩, h₃, h₄, _⟩;
  cases h₂; rcases h₂ with ⟨⟨k₂, a₂'⟩, h₅, h₆, _⟩; subst_vars;
  simp only at h₆ ⊢; subst_vars;
  { apply eq_of_union₂_ne_none _ h₃ h₅, simp [hl, hr] } <|>
  { exfalso, assumption } }

theorem exists_of_union₂_eq_none : ∀ {t₁ t₂ : trie α},
  t₁.union₂ t₂ = none →
  ∃ (k : pos_num) (a₁ a₂ : α), sigma.mk k a₁ ∈ t₁.to_list ∧ sigma.mk k a₂ ∈ t₂.to_list ∧ a₁ ≠ a₂
| nil                    nil                    := by simp [union₂]
| (node o₁        l₁ r₁) nil                    := by cases o₁; simp [union₂]
| nil                    (node o₂        l₂ r₂) := by cases o₂; simp [union₂]
| (node none      l₁ r₁) (node none      l₂ r₂) := λ h, by {
  simp only [union₂] at h,
  simp only [option.bind_eq_none, option.mem_def, option.bind_eq_some, not_exists, not_and] at h,
  simp only [to_list, list.mem_append, list.mem_map],
  cases hl : l₁.union₂ l₂ with l,
  { rcases exists_of_union₂_eq_none hl with ⟨k, a₁, a₂, hl⟩,
    existsi [k.bit0, a₁, a₂], simp [hl] },
  cases hr : r₁.union₂ r₂ with r,
  { rcases exists_of_union₂_eq_none hr with ⟨k, a₁, a₂, hr⟩,
    existsi [k.bit1, a₁, a₂], simp [hr] },
  exfalso,
  specialize h (node none l r) _ hl _ hr,
  simpa using h }
| (node (some a₁) l₁ r₁) (node none      l₂ r₂) := λ h, by {
  simp only [union₂] at h,
  simp only [option.bind_eq_none, option.mem_def, option.bind_eq_some, not_exists, not_and] at h,
  simp only [to_list, list.mem_append, list.mem_cons_iff, list.mem_map],
  cases hl : l₁.union₂ l₂ with l,
  { rcases exists_of_union₂_eq_none hl with ⟨k, a₁, a₂, hl⟩,
    existsi [k.bit0, a₁, a₂], simp [hl] },
  cases hr : r₁.union₂ r₂ with r,
  { rcases exists_of_union₂_eq_none hr with ⟨k, a₁, a₂, hr⟩,
    existsi [k.bit1, a₁, a₂], simp [hr] },
  exfalso,
  specialize h (node (some a₁) l r) _ hl _ hr,
  simpa using h }
| (node none      l₁ r₁) (node (some a₂) l₂ r₂) := λ h, by {
  simp only [union₂] at h,
  simp only [option.bind_eq_none, option.mem_def, option.bind_eq_some, not_exists, not_and] at h,
  simp only [to_list, list.mem_append, list.mem_cons_iff, list.mem_map],
  cases hl : l₁.union₂ l₂ with l,
  { rcases exists_of_union₂_eq_none hl with ⟨k, a₁, a₂, hl⟩,
    existsi [k.bit0, a₁, a₂], simp [hl] },
  cases hr : r₁.union₂ r₂ with r,
  { rcases exists_of_union₂_eq_none hr with ⟨k, a₁, a₂, hr⟩,
    existsi [k.bit1, a₁, a₂], simp [hr] },
  exfalso,
  specialize h (node (some a₂) l r) _ hl _ hr,
  simpa using h }
| (node (some a₁) l₁ r₁) (node (some a₂) l₂ r₂) := λ h, by {
  simp only [union₂] at h,
  split_ifs at h with heq, swap,
  { existsi [pos_num.one, a₁, a₂],
    simp [to_list, heq] },
  simp only [option.bind_eq_none, option.mem_def, option.bind_eq_some, not_exists, not_and] at h,
  simp only [to_list, list.mem_append, list.mem_cons_iff, list.mem_map],
  cases hl : l₁.union₂ l₂ with l,
  { rcases exists_of_union₂_eq_none hl with ⟨k, a₁, a₂, hl⟩,
    existsi [k.bit0, a₁, a₂], simp [hl] },
  cases hr : r₁.union₂ r₂ with r,
  { rcases exists_of_union₂_eq_none hr with ⟨k, a₁, a₂, hr⟩,
    existsi [k.bit1, a₁, a₂], simp [hr] },
  exfalso,
  specialize h (node (some a₁) l r) _ hl _ hr,
  simpa using h }

theorem mem_union₂_iff (t₁ t₂ : trie α) (s : (Σ _ : pos_num, α)) :
  (∃ (t : trie α), t₁.union₂ t₂ = some t ∧ s ∈ t.to_list) ↔
  (s ∈ t₁.to_list ∨ s ∈ t₂.to_list) ∧
  (∀ {k : pos_num} {a₁ a₂ : α},
     sigma.mk k a₁ ∈ t₁.to_list →
     sigma.mk k a₂ ∈ t₂.to_list →
     a₁ = a₂) :=
begin
  split,
  { rintro ⟨t, h⟩, split,
    { exact mem_or_mem_of_union₂ h.1 h.2},
    { intros _ _ _ h₁ h₂,
      exact eq_of_union₂_ne_none (option.ne_none_iff_exists'.2 ⟨_, h.1⟩) h₁ h₂ } },
  { rintro ⟨h₁, h₂⟩,
    cases h : t₁.union₂ t₂ with t,
    { exfalso,
      contrapose! h₂,
      apply exists_of_union₂_eq_none h },
    { cases h₁; existsi t; rw [eq_self_iff_true, true_and],
      { apply subset_of_union₂_left h h₁ },
      { apply subset_of_union₂_right h h₁ } } }
end

end union₂

section sdiff₂
variable [decidable_eq α]

/-- Remove key-values pairs from one trie that are also in another trie. -/
def sdiff₂ : trie α → trie α → trie α
| t₁                      nil                   := t₁
| nil                    _                      := nil
| (node o₁        l₁ r₁) (node none      l₂ r₂) := mk o₁ (l₁.sdiff₂ l₂) (r₁.sdiff₂ r₂)
| (node none      l₁ r₁) (node _         l₂ r₂) := mk none (l₁.sdiff₂ l₂) (r₁.sdiff₂ r₂)
| (node (some a₁) l₁ r₁) (node (some a₂) l₂ r₂) := mk (if a₁ = a₂ then none else some a₁)
                                                      (l₁.sdiff₂ l₂) (r₁.sdiff₂ r₂)

theorem sdiff₂_subset_left : ∀ (t₁ t₂ : trie α),
  (t₁.sdiff₂ t₂).to_list ⊆ t₁.to_list
| nil                    nil                    := by simp [sdiff₂, to_list]
| nil                    (node _         _  _)  := by simp [sdiff₂, to_list]
| (node o₁        _  _)  nil                    := by {
  cases o₁; simp [sdiff₂, to_list, list.subset_cons] }
| (node none      l₁ r₁) (node none      l₂ r₂) := λ _, by {
  simp only [sdiff₂, to_list, mk_to_list, list.mem_append],
  simp only [list.mem_map, sdiff₂_subset_left],
  rintro (⟨s', h₁, h₂⟩ | ⟨s', h₁, h₂⟩),
  { left, existsi s', tauto },
  { right, existsi s', tauto } }
| (node (some _)  l₁ r₁) (node none      l₂ r₂) := λ _, by {
  simp only [sdiff₂, to_list, mk_to_list, list.mem_append, list.mem_cons_iff],
  simp only [list.mem_map, sdiff₂_subset_left],
  rintro (h | ⟨s', h₁, h₂⟩ | ⟨s', h₁, h₂⟩),
  { left, exact h },
  { right, left, existsi s', tauto },
  { right, right, existsi s', tauto } }
| (node none      l₁ r₁) (node (some _)  l₂ r₂) := λ _, by {
  simp only [sdiff₂, to_list, mk_to_list, list.mem_append],
  simp only [list.mem_map, sdiff₂_subset_left],
  rintro (⟨s', h₁, h₂⟩ | ⟨s', h₁, h₂⟩),
  { left, existsi s', tauto },
  { right, existsi s', tauto } }
| (node (some a₁) l₁ r₁) (node (some a₂) l₂ r₂) := λ _, by {
  simp only [sdiff₂],
  split_ifs with h;
  simp only [to_list, mk_to_list, list.mem_append, list.mem_cons_iff];
  simp only [list.mem_map, sdiff₂_subset_left],
  { rintro (⟨s', h₁, h₂⟩ | ⟨s', h₁, h₂⟩),
    { right, left, existsi s', tauto },
    { right, right, existsi s', tauto }, },
  { rintro (h | ⟨s', h₁, h₂⟩ | ⟨s', h₁, h₂⟩),
    { left, exact h },
    { right, left, existsi s', tauto },
    { right, right, existsi s', tauto } } }

theorem not_mem_sdiff₂_of_mem_right : ∀ (t₁ t₂ : trie α) (s : (Σ _ : pos_num, α)),
  s ∈ t₂.to_list → s ∉ (t₁.sdiff₂ t₂).to_list
| nil                    nil                    := by simp [sdiff₂, to_list]
| nil                    (node _         _  _)  := by simp [sdiff₂, to_list]
| (node o₁        _  _)  nil                    := by {
  cases o₁; simp [sdiff₂, to_list, list.subset_cons] }
| (node none      l₁ r₁) (node none      l₂ r₂) := λ _, by {
  simp only [sdiff₂, to_list, mk_to_list, list.mem_append],
  simp only [list.mem_map],
  simp only [not_or_distrib, not_exists, not_and],
  rintro (⟨⟨⟩, h₁, h₂⟩ | ⟨⟨⟩, h₁, h₂⟩); split;
  { rintro ⟨⟩ h, contrapose! h,
    simp only [← h₂] at h,
    cases h, subst_vars, tauto } }
| (node (some _)  l₁ r₁) (node none      l₂ r₂) := λ _, by {
  simp only [sdiff₂, to_list, mk_to_list, list.mem_append, list.mem_cons_iff],
  simp only [list.mem_map],
  simp only [not_or_distrib, not_exists, not_and],
  rintro (⟨⟨⟩, h₁, h₂⟩ | ⟨⟨⟩, h₁, h₂⟩);
  { split,
    { simp [← h₂] },
    { split; {
        rintro ⟨⟩ h, contrapose! h,
        simp only [← h₂] at h,
        cases h, subst_vars, tauto } } } }
| (node none      l₁ r₁) (node (some _)  l₂ r₂) := λ _, by {
  simp only [sdiff₂, to_list, mk_to_list, list.mem_append, list.mem_cons_iff],
  simp only [list.mem_map],
  simp only [not_or_distrib, not_exists, not_and],
  rintro (h | h), { simp [h] },
  rcases h with (⟨⟨⟩, h₁, h₂⟩ | ⟨⟨⟩, h₁, h₂⟩); split;
  { rintro ⟨⟩ h, contrapose! h,
    simp only [← h₂] at h,
    cases h, subst_vars, tauto } }
| (node (some a₁) l₁ r₁) (node (some a₂) l₂ r₂) := λ _, by {
  simp only [sdiff₂],
  split_ifs with h';
  simp only [to_list, mk_to_list, list.mem_append, list.mem_cons_iff];
  simp only [list.mem_map];
  simp only [not_or_distrib, not_exists, not_and],
  { rintro (h | h), { simp [h] },
    rcases h with (⟨⟨⟩, h₁, h₂⟩ | ⟨⟨⟩, h₁, h₂⟩); split;
    { rintro ⟨⟩ h, contrapose! h,
      simp only [← h₂] at h,
      cases h, subst_vars, tauto } },
  { rintro (h | h), { rw [eq_comm] at h', simpa [h] },
    rcases h with (⟨⟨⟩, h₁, h₂⟩ | ⟨⟨⟩, h₁, h₂⟩);
    { split, { simp [← h₂] },
      split; {
        rintro ⟨⟩ h, contrapose! h,
        simp only [← h₂] at h,
        cases h, subst_vars, tauto } } } }

theorem mem_sdiff₂_of_mem_left_of_not_mem_right : ∀ {t₁ t₂ : trie α} {s : (Σ _ : pos_num, α)},
  s ∈ t₁.to_list →
  s ∉ t₂.to_list →
  s ∈ (t₁.sdiff₂ t₂).to_list
| nil                    nil                    := by simp [sdiff₂, to_list]
| nil                    (node _         _  _)  := by simp [sdiff₂, to_list]
| (node o₁        _  _)  nil                    := by {
  cases o₁; simp [sdiff₂, to_list, list.subset_cons] }
| (node none      l₁ r₁) (node none      l₂ r₂) := λ _, by {
  simp only [sdiff₂, to_list, mk_to_list, list.mem_append],
  simp only [list.mem_map, sdiff₂_subset_left],
  simp only [not_or_distrib, not_exists, not_and],
  rintro (⟨s', h₁, h₂⟩ | ⟨s', h₁, h₂⟩) ⟨h₃, h₄⟩,
  { left, existsi s', split,
    { apply mem_sdiff₂_of_mem_left_of_not_mem_right h₁, tauto },
    { exact h₂ } },
  { right, existsi s', split,
    { apply mem_sdiff₂_of_mem_left_of_not_mem_right h₁, tauto },
    { exact h₂ } } }
| (node (some _)  l₁ r₁) (node none      l₂ r₂) := λ _, by {
  simp only [sdiff₂, to_list, mk_to_list, list.mem_append, list.mem_cons_iff],
  simp only [list.mem_map, sdiff₂_subset_left],
  simp only [not_or_distrib, not_exists, not_and],
  rintro (h | ⟨s', h₁, h₂⟩ | ⟨s', h₁, h₂⟩) ⟨h₃, h₄⟩,
  { left, exact h },
  { right, left, existsi s', split,
    { apply mem_sdiff₂_of_mem_left_of_not_mem_right h₁, tauto },
    { exact h₂ } },
  { right, right, existsi s', split,
    { apply mem_sdiff₂_of_mem_left_of_not_mem_right h₁, tauto },
    { exact h₂ } } }
| (node none      l₁ r₁) (node (some _)  l₂ r₂) := λ _, by {
   simp only [sdiff₂, to_list, mk_to_list, list.mem_append, list.mem_cons_iff],
   simp only [list.mem_map, sdiff₂_subset_left],
   simp only [not_or_distrib, not_exists, not_and],
   rintro (⟨s', h₁, h₂⟩ | ⟨s', h₁, h₂⟩) ⟨h₃, h₄, h₅⟩,
   { left, existsi s', split,
    { apply mem_sdiff₂_of_mem_left_of_not_mem_right h₁, tauto },
    { exact h₂ } },
   { right, existsi s', split,
    { apply mem_sdiff₂_of_mem_left_of_not_mem_right h₁, tauto },
    { exact h₂ } } }
| (node (some a₁) l₁ r₁) (node (some a₂) l₂ r₂) := λ _, by {
  simp only [sdiff₂],
  split_ifs with h;
  simp only [to_list, mk_to_list, list.mem_append, list.mem_cons_iff];
  simp only [list.mem_map];
  simp only [not_or_distrib, not_exists, not_and];
  rintro (h | ⟨s', h₁, h₂⟩ | ⟨s', h₁, h₂⟩) ⟨h₃, h₄, h₅⟩,
  { cc },
  { left, existsi s', split,
    { apply mem_sdiff₂_of_mem_left_of_not_mem_right h₁, tauto },
    { exact h₂ } },
  { right, existsi s', split,
    { apply mem_sdiff₂_of_mem_left_of_not_mem_right h₁, tauto },
    { exact h₂ } },
  { cc },
  { right, left, existsi s', split,
    { apply mem_sdiff₂_of_mem_left_of_not_mem_right h₁, tauto },
    { exact h₂ } },
  { right, right, existsi s', split,
    { apply mem_sdiff₂_of_mem_left_of_not_mem_right h₁, tauto },
    { exact h₂ } } }

theorem mem_sdiff₂_iff (t₁ t₂ : trie α) (s : (Σ _ : pos_num, α)) :
  s ∈ (t₁.sdiff₂ t₂).to_list ↔ (s ∈ t₁.to_list ∧ s ∉ t₂.to_list) :=
begin
  split; intro h,
  { split,
    { apply sdiff₂_subset_left, assumption },
    { contrapose! h, apply not_mem_sdiff₂_of_mem_right, assumption } },
  { apply mem_sdiff₂_of_mem_left_of_not_mem_right; tauto }
end

end sdiff₂

section filter_map
variable {β : Type u}

/-- This combines filter and map, by applying the map function to the value of each element.
The resulting entry is is removed from the new trie if the value is none, or added otherwise. -/
def filter_map (f : α → option β) : trie α → trie β
| nil          := nil
| (node a l r) := mk (a >>= f) l.filter_map r.filter_map

theorem mem_filter_map_iff (f : α → option β) : ∀ (t : trie α) (s : (Σ _ : pos_num, β)),
  s ∈ (t.filter_map f).to_list ↔ ∃ (a : α), (⟨s.1, a⟩ : (Σ _, α)) ∈ t.to_list ∧ f a = some s.2
| nil          := by simp [filter_map, to_list]
| (node o l r) := λ s, by {
  have hiff:
    s ∈ map_bit0 (l.filter_map f).to_list ++ map_bit1 (r.filter_map f).to_list ↔
    ∃ a, (⟨s.1, a⟩ : Σ _, α) ∈ (map_bit0 l.to_list ++ map_bit1 r.to_list) ∧ f a = some s.2,
  { simp only [list.mem_append, list.mem_map, heq_iff_eq],
    simp only [mem_filter_map_iff],
    split,
    { rintro (⟨s₂, ⟨⟨a, h₁, h₂⟩, ⟨⟩⟩⟩ | ⟨s₂, ⟨⟨a, h₁, h₂⟩, ⟨⟩⟩⟩);
      { existsi a, simp [h₁, h₂] } },
    { cases s with k b,
      rintro ⟨a, ⟨(⟨s₁, ⟨h₁, ⟨⟩, ⟨⟩⟩⟩ | ⟨s₁, ⟨h₁, ⟨⟩, ⟨⟩⟩⟩), h₂⟩⟩,
      { left,
        existsi (⟨s₁.1, b⟩ : (Σ _, β)),
        split, existsi s₁.2, simp [h₁, h₂] },
      { right,
        existsi (⟨s₁.1, b⟩ : (Σ _, β)),
        split, existsi s₁.2, simp [h₁, h₂] } } },

  simp only [filter_map, mk_to_list],
  cases o with a,
  { simp only [(>>=), option.bind, to_list], rw [hiff] },
  { cases hf : f a with b; simp only [hf, (>>=), option.bind, to_list, list.mem_cons_iff, heq_iff_eq]; rw [hiff],
    { split,
      { rintro ⟨a', h₁, h₂⟩,
        existsi a', simp [h₁, h₂] },
      { rintro ⟨a', (⟨h₁, h₂⟩ | h₁), h⟩,
        { subst h₂, rw h at hf, cases hf },
        { existsi a', simp [h₁, h] } } },
    { split,
      { rintro (h | ⟨a', h₁, h₂⟩),
        { cases h, existsi a, simp [hf] },
        { existsi a', simp [h₁, h₂] } },
      { rintro ⟨a', (⟨h₁, h₂⟩ | h₁), h⟩,
        { left, subst a', cases s, cc },
        { right, existsi a', simp [h₁, h] } } } } }

end filter_map

section filter_map₂
variables {β γ : Type*}

/-- This combines filter and map over two tries, by applying the map function to the values of
each key. The result is none if some key is present in the first trie but not the second. -/
def filter_map₂ (f : α → β → option γ) : trie α → trie β → option (trie γ)
| nil                   _                     := some nil
| (node none     la ra) (node _        lb rb) := do
  l ← filter_map₂ la lb,
  r ← filter_map₂ ra rb,
  some $ mk none l r
| (node (some a) la ra) (node (some b) lb rb) := do
  l ← filter_map₂ la lb,
  r ← filter_map₂ ra rb,
  some $ mk (f a b) l r
| ta                    nil                   := if ta.null then some nil else none
| _                     _                     := none

theorem exists_of_filter_map₂_eq_some {f : α → β → option γ} : ∀ {ta : trie α} {tb : trie β}
                                                                 {t : trie γ}
                                                                 {s : (Σ _ : pos_num, γ)},
  filter_map₂ f ta tb = some t →
  s ∈ t.to_list →
  ∃ (a : α) (b : β),
    (⟨s.1, a⟩ : (Σ _, α)) ∈ ta.to_list ∧
    (⟨s.1, b⟩ : (Σ _, β)) ∈ tb.to_list ∧
    f a b = some s.2
| nil                   tb                    := λ _ _ h st, by {
  exfalso,
  cases tb; {
    simp only [filter_map₂] at h, subst h,
    simpa [to_list] using st } }
| (node oa       la ra) nil                   := λ t s h st, by {
  cases oa; {
    simp only [filter_map₂] at h,
    split_ifs at h; exfalso; subst_vars,
    { simpa [to_list] using st },
    { exact h } } }
| (node none     la ra) (node ob      lb rb) := λ t s h, by {
  simp only [filter_map₂, option.bind_eq_some] at h,
  rcases h with ⟨l, hl, r, hr, h⟩, subst h,
  cases ob; {
    simp only [mk_to_list, to_list],
    simp only [list.mem_append, list.mem_map],
    rintro (⟨s', h, _⟩ | ⟨s', h, _⟩); subst_vars,
    { rcases exists_of_filter_map₂_eq_some hl h with ⟨a', b', h⟩,
      existsi [a', b'], simp [h] },
    { rcases exists_of_filter_map₂_eq_some hr h with ⟨a', b', h⟩,
      existsi [a', b'], simp [h] } } }
| (node (some _) la ra) (node none     lb rb) := by simp [filter_map₂]
| (node (some a) la ra) (node (some b) lb rb) := λ t s h, by {
  simp only [filter_map₂, option.bind_eq_some] at h,
  rcases h with ⟨l, hl, r, hr, h⟩, subst h,
  suffices :
    s ∈ map_bit0 l.to_list ++ map_bit1 r.to_list →
    ∃ (a' : α) (b' : β),
      (s.1 = 1 ∧ a' = a ∨ (⟨s.1, a'⟩ : (Σ _, α)) ∈ map_bit0 la.to_list ++ map_bit1 ra.to_list) ∧
      (s.1 = 1 ∧ b' = b ∨ (⟨s.1, b'⟩ : (Σ _, β)) ∈ map_bit0 lb.to_list ++ map_bit1 rb.to_list) ∧
      f a' b' = some s.2,
  { cases hf : f a b with c;
    simp only [hf, mk_to_list, to_list, list.mem_cons_iff, heq_iff_eq],
    { assumption },
    { rintro (h | h),
      { subst h, simp [hf] },
      { revert h, assumption } } },

  simp only [list.mem_append, list.mem_map],
  rintro (⟨s', h, _⟩ | ⟨s', h, _⟩); subst_vars,
  { rcases exists_of_filter_map₂_eq_some hl h with ⟨a', b', h⟩,
    existsi [a', b'], simp [h] },
  { rcases exists_of_filter_map₂_eq_some hr h with ⟨a', b', h⟩,
    existsi [a', b'], simp [h] } }

theorem subset_of_filter_map₂_ne_none {f : α → β → option γ} : ∀ {ta : trie α} {tb : trie β},
  filter_map₂ f ta tb ≠ none →
  ta.to_list.keys ⊆ tb.to_list.keys
| nil                   tb                    := λ h, by simp [to_list]
| (node none     la ra) nil                   := λ h k, by {
  have hnil : la.to_list = list.nil ∧ ra.to_list = list.nil,
  { simpa [filter_map₂, null_iff, to_list, mem_keys_append] using h },
  cases hnil with hla hra,
  simp [hla, hra, to_list, list.mem_keys] }
| (node (some _) la ra) nil                   := by simp [filter_map₂, null_iff, to_list]
| (node oa       la ra) (node ob       lb rb) := λ h k, by {
  rw [option.ne_none_iff_exists'] at h,
  cases oa; cases ob; simp only [filter_map₂, option.bind_eq_some] at h;
  rcases h with ⟨t, ta, hta, tb, htb, h⟩;
  simp only [to_list, list.keys_cons, list.mem_cons_iff, mem_keys_append];
  { cases k,
    case pos_num.one { simp [list.keys] },
    case pos_num.bit0 {
      simp only [bit0_mem_map_bit0_keys, bit0_not_mem_map_bit1_keys, false_or, or_false],
      apply subset_of_filter_map₂_ne_none (option.ne_none_iff_exists'.2 ⟨_, hta⟩) },
    case pos_num.bit1 {
      simp only [bit1_mem_map_bit1_keys, bit1_not_mem_map_bit0_keys, false_or],
      apply subset_of_filter_map₂_ne_none (option.ne_none_iff_exists'.2 ⟨_, htb⟩) } } }

theorem filter_map₂_ne_none_of_subset {f : α → β → option γ} : ∀ {ta : trie α} {tb : trie β},
  ta.to_list.keys ⊆ tb.to_list.keys →
  filter_map₂ f ta tb ≠ none
| nil                   tb                    := by cases tb; simp [filter_map₂]
| (node none     la ra) nil                   := λ h, by {
  simp only [to_list, list.keys_nil] at h,
  have h' := list.eq_nil_of_subset_nil h,
  rw [list.keys, list.map_eq_nil, list.append_eq_nil] at h',
  simp only [filter_map₂, null_iff, to_list],
  cases h' with h₁ h₂, simp [h₁, h₂] }
| (node (some _) la ra) nil                   := by simp [to_list]
| (node oa       la ra) (node ob       lb rb) := λ h, by {
  cases oa; cases ob,
  case option.some option.none {
    exfalso,
    simpa [to_list, list.keys] using h },
  all_goals {
    simp only [to_list] at h,
    simp only [list.keys, list.map_append, list.map_cons, list.append_subset_iff, list.cons_subset,
               list.mem_cons_self, true_and] at h,
    repeat { rw [← list.keys] at h },
    try { rw [list.subset_cons_iff_subset (one_not_mem_keys_map_bit0 _),
              list.subset_cons_iff_subset (one_not_mem_keys_map_bit1 _)] at h },
    have h₁ := (list.subset_append_iff_subset_left (map_bit0_bit1_disjoint_keys _ _)).1 h.1,
    rw [map_bit0_keys_subset_map_bit0_keys_iff] at h₁,
    have h₂ := (list.subset_append_iff_subset_right (map_bit0_bit1_disjoint_keys _ _).symm).1 h.2,
    rw [map_bit1_keys_subset_map_bit1_keys_iff] at h₂,
    rcases option.ne_none_iff_exists'.1 (filter_map₂_ne_none_of_subset h₁) with ⟨l, hl⟩,
    rcases option.ne_none_iff_exists'.1 (filter_map₂_ne_none_of_subset h₂) with ⟨r, hr⟩,
    simp only [filter_map₂, ne.def, option.bind_eq_none, option.bind_eq_some, option.mem_def,
               not_forall, not_not, exists_prop],
    tauto } }

theorem mem_of_filter_map₂ {f : α → β → option γ} : ∀ {ta : trie α} {tb : trie β} {t : trie γ}
                                                      {k : pos_num} {a : α} {b : β} {c : γ},
  filter_map₂ f ta tb = some t →
  sigma.mk k a ∈ ta.to_list →
  sigma.mk k b ∈ tb.to_list →
  f a b = some c →
  sigma.mk k c ∈ t.to_list
| nil                   nil                   := λ _ _ _ _ _ _, by simp [to_list]
| nil                   (node _        lb rb) := λ _ _ _ _ _ _, by simp [to_list]
| (node oa       la ra) nil                   := λ _ _ _ _ _ _, by simp [to_list]
| (node none     la ra) (node ob       lb rb) := λ _ k a b c h, by {
  simp only [filter_map₂, option.bind_eq_some] at h,
  rcases h with ⟨l, hl, r, hr, ht⟩, subst ht,
  suffices :
    ((∃ (ka : pos_num), sigma.mk ka a ∈ la.to_list ∧ ka.bit0 = k) ∨
      ∃ (ka : pos_num), sigma.mk ka a ∈ ra.to_list ∧ ka.bit1 = k) →
    ((∃ (kb : pos_num), sigma.mk kb b ∈ lb.to_list ∧ kb.bit0 = k) ∨
      ∃ (kb : pos_num), sigma.mk kb b ∈ rb.to_list ∧ kb.bit1 = k) →
    f a b = some c →
    (∃ (kc : pos_num), sigma.mk kc c ∈ l.to_list ∧ kc.bit0 = k) ∨
    (∃ (kc : pos_num), sigma.mk kc c ∈ r.to_list ∧ kc.bit1 = k),
  { cases ob;
    simp only [to_list, mk_to_list, list.mem_cons_iff, list.mem_append, list.mem_map];
    simp only [exists_eq_right_right, sigma.exists, heq_iff_eq],
    { assumption },
    { intro h₁, rintro (⟨⟨⟩, ⟨⟩⟩ | h₂), { exfalso, simpa using h₁ },
      revert h₁ h₂, assumption } },

  rintro (h₁ | h₁) (h₂ | h₂) h₃;
  rcases h₁ with ⟨k₁, h₁, _⟩;
  rcases h₂ with ⟨k₂, h₂, hk⟩;
  subst_vars; simp only at hk,
  { subst hk,
    suffices : sigma.mk k₂ c ∈ l.to_list, by simpa,
    exact mem_of_filter_map₂ hl h₁ h₂ h₃, },
  { exfalso, exact hk },
  { exfalso, exact hk },
  { subst hk,
    suffices : sigma.mk k₂ c ∈ r.to_list, by simpa,
    exact mem_of_filter_map₂ hr h₁ h₂ h₃ } }
| (node (some _) la ra) (node none     lb rb) := by simp [filter_map₂]
| (node (some a) la ra) (node (some b) lb rb) := λ _ _ x y c h, by {
  simp only [filter_map₂, option.bind_eq_some] at h,
  rcases h with ⟨l, hl, r, hr, ht⟩, subst ht,
  cases hf : f a b;
  simp only [to_list, mk_to_list, list.mem_cons_iff, list.mem_append, list.mem_map];
  simp only [exists_eq_right_right, sigma.exists, heq_iff_eq];
  { rintro (⟨_, _⟩ | h₁),
    { subst_vars,
      simp only [eq_self_iff_true, true_and, and_false, or_false, false_and, exists_false],
      cc },
    rintro (⟨_, _⟩ | h₂),
    { exfalso, subst_vars, simpa using h₁ },
    intro h₃,
    cases h₁; rcases h₁ with ⟨ka, h₁, _⟩;
    cases h₂; rcases h₂ with ⟨kb, h₂, hk⟩;
    subst_vars; simp only at hk; subst_vars,
    { suffices : sigma.mk kb c ∈ l.to_list, by simpa,
      exact mem_of_filter_map₂ hl h₁ h₂ h₃ },
    { exfalso, assumption },
    { exfalso, assumption },
    { suffices : sigma.mk kb c ∈ r.to_list, by simpa,
      exact mem_of_filter_map₂ hr h₁ h₂ h₃ } } }

theorem mem_filter_map₂_iff (f : α → β → option γ) (ta : trie α) (tb : trie β) (s : (Σ _ : pos_num, γ)) :
  (∃ (t : trie γ), filter_map₂ f ta tb = some t ∧ s ∈ t.to_list) ↔
  (∃ (a : α) (b : β),
    (⟨s.1, a⟩ : (Σ _, α)) ∈ ta.to_list ∧
    (⟨s.1, b⟩ : (Σ _, β)) ∈ tb.to_list ∧
    f a b = some s.2) ∧
  ta.to_list.keys ⊆ tb.to_list.keys :=
begin
  split,
  { rintro ⟨t, h⟩, split,
    { exact exists_of_filter_map₂_eq_some h.1 h.2 },
    { exact subset_of_filter_map₂_ne_none (option.ne_none_iff_exists'.2 ⟨_, h.1⟩) } },
  { rintro ⟨⟨a, b, h₁, h₂, h₃⟩, h₄⟩,
    cases h : filter_map₂ f ta tb with t,
    { exfalso,
      contrapose h,
      exact filter_map₂_ne_none_of_subset h₄ },
    { existsi t,
      rw [eq_self_iff_true, true_and],
      cases s,
      exact mem_of_filter_map₂ h h₁ h₂ h₃ } }
end

end filter_map₂

end trie
