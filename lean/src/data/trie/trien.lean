/-
Copyright (c) 2021 The UNSAT Group. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luke Nelson, Xi Wang
-/
import .basic
import misc.vector

/-!
# Nested binary tries

This file provides an implementation of nested tries of arbitrary (finite) depth,

They are indexed by a sequence of `pos_num`s for each level of the trien.

-/

/--
`trien α n` is `n + 1` nested `trie`s with `α` as the final return type.
For example, `trien α 2` is `trie (trie (trie α))`.
They are indexed using vectors of `pos_num`: one `pos_num` for each level of `trie`.
 -/
@[irreducible]
def trien (α : Type*) : ∀ (n : ℕ), Type*
| 0       := trie α
| (n + 1) := trie (trien n)

namespace trien
local attribute [semireducible] trien
variable {α : Type*}

/-- The empty trien. -/
def nil : ∀ {n : ℕ}, trien α n
| 0       := trie.nil
| (n + 1) := trie.nil

instance {n : ℕ} : inhabited (trien α n) := ⟨nil⟩

/-- Flatten a trien into a list of ⟨key, value⟩ pairs, where keys are vectors of indices. -/
def to_list : ∀ {n : ℕ}, trien α n → list (Σ (_ : vector pos_num (n + 1)), α)
| 0       t := (trie.to_list t).map (λ x, ⟨x.1 ::ᵥ vector.nil, x.2⟩)
| (n + 1) t := trie.to_list t >>= λ x, (@to_list n x.2).map (λ y, ⟨x.1 ::ᵥ y.1, y.2⟩)

/-- Desctructively update (or insert) a value into a trien given a vector of indices. -/
def update : ∀ {n : ℕ} (t : trien α n) (v : vector pos_num (n + 1)) (x : α), trien α n
| 0       t v x := trie.update v.head x t
| (n + 1) t v x :=
  let subtree : trien α n := (t.lookup v.head).get_or_else nil in
  trie.update v.head (@update n subtree v.tail x) t

/-- Lookup an element from a trien given a vector of indices. -/
def lookup : ∀ {n : ℕ} (t : trien α n) (v : vector pos_num (n + 1)), option α
| 0       t v := trie.lookup v.head t
| (n + 1) t v := trie.lookup v.head t >>= λ t', @lookup n t' v.tail

section repr
variables [has_repr α] {n : ℕ}

/-- `repr` simply prints the list version of the trien. -/
private def repr (t : trien α n) : string :=
repr $ t.to_list.map (λ p, (p.1.to_list, p.2))

instance : has_repr (trien α n) := ⟨repr⟩

end repr

theorem lookup_nil : ∀ {n : ℕ} {v : vector pos_num (n + 1)},
  lookup (nil : trien α n) v = none
| 0       v := by {
  simp only [nil, lookup],
  rw [option.eq_none_iff_forall_not_mem],
  intros a h,
  rw [trie.mem_lookup_iff] at h,
  cases h }
| (n + 1) v := by {
  simp only [lookup, option.bind_eq_none, option.mem_def],
  intros _ _ h,
  rw [← option.mem_def, trie.mem_lookup_iff] at h,
  cases h }

theorem mem_lookup_iff : ∀ {n : ℕ} (k : vector pos_num (n + 1)) (v : α) (t : trien α n),
  v ∈ t.lookup k ↔ sigma.mk k v ∈ to_list t
| 0 k v t := by {
  simp only [lookup, to_list, trie.mem_lookup_iff],
  rw [← vector.cons_head_tail k],
  simp only [list.mem_map, exists_eq_right_right, sigma.exists, vector.singleton_tail, heq_iff_eq],
  rw [vector.head_cons],
  split; intros h,
  { existsi k.head,
    refine and.intro h rfl },
  { rcases h with ⟨a, h₁, h₂⟩,
    rw vector.cons_inj at h₂,
    cc } }
| (n + 1) k v t := by {
  rw [lookup],
  simp only [option.bind_eq_some, option.mem_def],
  simp_rw [← option.mem_def, mem_lookup_iff, trie.mem_lookup_iff],
  simp only [to_list, exists_prop, list.mem_map, exists_eq_right_right, list.bind_eq_bind, sigma.exists, list.mem_bind, heq_iff_eq],
  split; intros h,
  { rcases h with ⟨a, h₁, h₂⟩,
    existsi k.head,
    existsi a,
    refine and.intro h₁ _,
    existsi k.tail,
    refine and.intro h₂ _,
    simp only [vector.cons_head_tail] },
  { rcases h with ⟨a, b, h₁, a', h₂, h₃⟩,
    existsi b,
    subst h₃,
    rw [vector.cons_head, vector.cons_tail],
    refine and.intro h₁ h₂ } }

theorem not_mem_nil : ∀ {n : ℕ} {k : vector pos_num (n + 1)} {v : α},
  sigma.mk k v ∉ (nil : trien α n).to_list
| 0 k v := by {
  simp only [nil, to_list],
  rw [list.mem_map],
  push_neg,
  intros a h,
  cases h }
| (n + 1) k v := by {
  simp only [nil, to_list],
  simp only [not_exists, exists_prop, list.mem_map, not_and, exists_eq_right_right, list.bind_eq_bind, sigma.exists, list.mem_bind,
             heq_iff_eq],
  intros _ _ h,
  cases h }

/-- An eliminator for disjunction that gives you the negation of the other
    disjunct in one of the cases. -/
private theorem classical_disjunction_elimination {P Q R : Prop} :
  (P → R) →
  (¬P → Q → R) →
  (P ∨ Q) → R :=
begin
  intros a b c,
  cases c,
  { tauto },
  by_cases P; tauto
end

theorem mem_update_iff : ∀ {n : ℕ} (k : vector pos_num (n + 1)) (v : α) (t : trien α n) (s : (Σ _ : (vector pos_num (n + 1)), α)),
  s ∈ to_list (t.update k v) ↔ (if s.1 = k then s.2 = v else s ∈ t.to_list)
| 0 k v t ⟨k', v'⟩ := by {
  simp only [to_list, update, list.mem_map],
  simp_rw [trie.mem_update_iff],
  split_ifs with not_eq is_eq; subst_vars,
  { split; intros h; subst_vars,
    { rcases h with ⟨a, h₁, h₂, h₃⟩,
      cases a with k'' v'',
      subst h₃,
      subst h₂,
      rw if_pos at h₁,
      by from h₁,
      by refl },
    { existsi (⟨k'.head, v'⟩ : Σ (_ : pos_num), α),
      rw if_pos,
      swap, refl,
      refine and.intro rfl (and.intro _ (by refl)),
      rw [← vector.singleton_tail k', vector.cons_head_tail] } },
  { split; intros h,
    { rcases h with ⟨a, h₁, h₂, h₃⟩,
      cases a with k'' v'',
      subst h₃,
      subst h₂,
      rw if_neg at h₁,
      { existsi (⟨k'', v''⟩ : Σ (_ : pos_num), α),
        refine and.intro h₁ (and.intro rfl heq.rfl) },
      { contrapose! not_eq,
        rw [not_eq, ← vector.singleton_tail k, vector.cons_head_tail] } },
    { rcases h with ⟨a, h₁, h₂, h₃⟩,
      cases a with k'' v'',
      subst h₂,
      subst h₃,
      existsi (⟨k'', v''⟩ : Σ (_ : pos_num), α),
      rw if_neg,
      { refine and.intro h₁ (and.intro rfl heq.rfl) },
      { contrapose! not_eq,
        rw [not_eq, ← vector.singleton_tail k, vector.cons_head_tail] } } } }
| (n + 1) k v t ⟨k', v'⟩ := by {
  simp only [update, to_list],
  simp only [exists_prop, list.mem_map, exists_eq_right_right, list.bind_eq_bind, sigma.exists, list.mem_bind, heq_iff_eq,
             sigma.mk.inj_iff, list.map],
  split; intros h,
  { rcases h with ⟨a, b, h₁, h₂, k'', h₃⟩; subst_vars,
    rw [trie.mem_update_iff] at h₁,
    split_ifs at h₁ with h_eq,
    { simp only at h_eq,
      subst h_eq,
      subst h₁,
      rw [mem_update_iff] at k'',
      split_ifs at k'' with h_eq₂,
      { simp only at h_eq₂,
        subst h_eq₂,
        rw [if_pos],
        by assumption,
        by rw [vector.cons_head_tail] },
      { rw [if_neg], swap,
        { contrapose! h_eq₂,
          rw [← h_eq₂, vector.cons_tail] },
        cases l : trie.lookup k.head t,
        { rw [l] at k'',
          exfalso,
          apply not_mem_nil k'' },
        rw [l, option.get_or_else_some] at k'',
        rw [← option.mem_def, trie.mem_lookup_iff] at l,
        existsi k.head,
        existsi val,
        refine and.intro l _,
        existsi h₂,
        refine and.intro k'' rfl } },
    { rw [if_neg], swap,
      { contrapose! h_eq,
        rw [← h_eq, vector.cons_head] },
      existsi a,
      existsi b,
      refine and.intro h₁ _,
      existsi h₂,
      refine and.intro k'' rfl } },
  { split_ifs at h with h_eq; subst_vars,
    { existsi k'.head,
      existsi _,
      split,
      { rw [trie.mem_update_iff, if_pos],
        refl },
      { existsi k'.tail,
        refine and.intro _ (by rw [vector.cons_head_tail]),
        rw [mem_update_iff, if_pos],
        refl } },
    { rcases h with ⟨a, b, h₁, h₂, k'', h₃⟩; subst_vars,
      have h_k := vector.cons_neq_iff a h₂ k,
      simp only [ne] at h_k,
      rw h_k at h_eq,
      clear h_k,
      existsi a,
      refine classical_disjunction_elimination _ _ h_eq; intros h_eq₁,
      { existsi b,
        split, swap,
        { existsi h₂,
          refine and.intro k'' rfl },
        rw [trie.mem_update_iff, if_neg],
        from h₁,
        from h_eq₁ },
      { intros h_eq₂,
        push_neg at h_eq₁,
        subst h_eq₁,
        existsi b.update k.tail v,
        split,
        { rw [trie.mem_update_iff, if_pos],
          swap, by refl,
          rw [← trie.mem_lookup_iff, option.mem_def] at h₁,
          rw [h₁],
          refl },
        existsi h₂,
        refine and.intro _ rfl,
        rw [mem_update_iff, if_neg],
        by from k'',
        by from h_eq₂ } } } }

end trien
