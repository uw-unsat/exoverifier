/-
Copyright (c) 2021 The UNSAT Group. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luke Nelson, Xi Wang
-/
import data.list

namespace list

theorem nth_append_eq_ite {α : Type*} {l r : list α} {i : ℕ} :
  (l ++ r).nth i = if (i < l.length) then (l.nth i) else (r.nth (i - l.length)) :=
begin
  split_ifs,
  { rw [list.nth_append], tauto },
  { rw [list.nth_append_right],
    rw [not_lt] at h,
    from h }
end

section subset
variable {α : Type*}

theorem subset_cons_iff_subset {a : α} {l₁ l₂ : list α} (h : a ∉ l₁) :
  l₁ ⊆ (a :: l₂) ↔
  l₁ ⊆ l₂ :=
begin
  simp only [subset_def, mem_cons_iff],
  split,
  { intros h' a' a'l₁,
    specialize h' a'l₁,
    cases h',
    { subst h', exfalso, tauto },
    { tauto } },
  { tauto }
end

theorem subset_append_iff_subset_left {l₁ l₂ l₃ : list α} (d : list.disjoint l₁ l₃) :
  l₁ ⊆ l₂ ++ l₃ ↔
  l₁ ⊆ l₂ :=
begin
  simp only [subset_def, mem_append],
  split,
  { intros h a al₁,
    specialize h al₁,
    tauto },
  { tauto }
end

theorem subset_append_iff_subset_right {l₁ l₂ l₃ : list α} (d : list.disjoint l₁ l₂) :
  l₁ ⊆ l₂ ++ l₃ ↔
  l₁ ⊆ l₃ :=
begin
  simp only [subset_def, mem_append],
  split,
  { intros h a al₁,
    specialize h al₁,
    tauto },
  { tauto }
end

end subset

namespace sigma
variables {α : Type*} [decidable_eq α] {β : α → Type*}

def find (x : α) (p : β x → Prop) [decidable_pred p] : list (sigma β) → option (β x)
| [] := none
| (⟨x', v⟩ :: xs) :=
  if h : x' = x
  then let v' : β x := h.rec v in
       if p v' then v' else find xs
  else find xs

lemma find_some {x : α} {p : β x → Prop} [decidable_pred p] {l : list (sigma β)} {v : β x}
  (H : find x p l = some v) : p v :=
begin
  induction l,
  case list.nil { cases H },
  case list.cons : hd tl {
    cases hd with x' v,
    rw [find] at H,
    split_ifs at H; subst_vars; try{tauto},
    cases H,
    simp only at h_1,
    assumption }
end

lemma find_mem {x : α} {p : β x → Prop} [decidable_pred p] {l : list (sigma β)} {v : β x}
  (H : find x p l = some v) : sigma.mk x v ∈ l :=
begin
  induction l,
  case list.nil { cases H },
  case list.cons : hd tl {
    rw [list.mem_cons_iff],
    cases hd with x' v,
    rw [find] at H,
    split_ifs at H; subst_vars; try{tauto},
    cases H,
    tauto }
end

end sigma
end list
