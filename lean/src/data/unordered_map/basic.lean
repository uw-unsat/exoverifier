/-
Copyright (c) 2021 The UNSAT Group. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luke Nelson, Xi Wang
-/
import data.list.sigma

/-- Typeclass for unordered maps. -/
class unordered_map (α β : out_param Type*) (σ : Type*) :=
(to_list : σ → list (Σ _ : α, β))
(nodupkeys : ∀ (m : σ), (to_list m).nodupkeys)
(elems : σ → list β)
(mem_elems_iff : ∀ (m : σ) (b : β), b ∈ elems m ↔ ∃ (a : α), sigma.mk a b ∈ to_list m)
(empty : σ)
(empty_eq : to_list empty = [])
(null : σ → bool)
(null_iff : ∀ (m : σ),
  null m ↔ to_list m = [])
(unsingleton : σ → option (Σ _ : α, β))
(unsingleton_iff : ∀ (m : σ) (s : (Σ _ : α, β)),
  unsingleton m = some s ↔ to_list m = [s])
(card : σ → ℕ)
(card_eq : ∀ (m : σ),
  card m = (to_list m).length)
(lookup [decidable_eq α] : α → σ → option β)
(mem_lookup_iff [decidable_eq α] : ∀ (a : α) (b : β) (m : σ),
  b ∈ lookup a m ↔ sigma.mk a b ∈ to_list m)
(kinsert [decidable_eq α] : α → β → σ → σ)
(mem_kinsert_iff [decidable_eq α] : ∀ (a : α) (b : β) (m : σ) (s : (Σ _ : α, β)),
  s ∈ to_list (kinsert a b m) ↔ s ∈ to_list m ∨ (a ∉ (to_list m).keys ∧ s = ⟨a, b⟩))
(insert₂ [decidable_eq α] [decidable_eq β] : α → β → σ → σ)
(mem_insert₂_iff [decidable_eq α] [decidable_eq β] : ∀ (a : α) (b : β) (m : σ) (s : (Σ _ : α, β)),
  s ∈ to_list (insert₂ a b m) ↔
  (s = ⟨a, b⟩ ∨ s ∈ to_list m) ∧ (a ∈ (to_list m).keys → sigma.mk a b ∈ to_list m))
(kerase [decidable_eq α] : σ → α → σ)
(mem_kerase_iff [decidable_eq α] : ∀ (m : σ) (a : α) (s : (Σ _ : α, β)),
  s ∈ to_list (kerase m a) ↔ s.1 ≠ a ∧ s ∈ to_list m)
(erase₂ [decidable_eq α] [decidable_eq β] : σ → α → β → σ)
(mem_erase₂_iff [decidable_eq α] [decidable_eq β] : ∀ (m : σ) (a : α) (b : β) (s : (Σ _ : α, β)),
  s ∈ to_list (erase₂ m a b) ↔ s ≠ ⟨a, b⟩ ∧ s ∈ to_list m)
(filter_map : (β → option β) → σ → σ)
(mem_filter_map_iff (f : β → option β) : ∀ (m : σ) (s : (Σ _ : α, β)),
  s ∈ to_list (filter_map f m) ↔ ∃ b, (⟨s.1, b⟩ : (Σ _ : α, β)) ∈ to_list m ∧ f b = some s.2)
(ksdiff [decidable_eq α] : σ → σ → σ)
(mem_ksdiff_iff [decidable_eq α] : ∀ (m₁ m₂ : σ) (s : (Σ _ : α, β)),
  s ∈ to_list (ksdiff m₁ m₂) ↔ s ∈ to_list m₁ ∧ s.1 ∉ (to_list m₂).keys)
(union₂ [decidable_eq α] [decidable_eq β] : σ → σ → option σ)
(mem_union₂_iff [decidable_eq α] [decidable_eq β] : ∀ (m₁ m₂ : σ) (s : (Σ _ : α, β)),
  (∃ (m : σ), union₂ m₁ m₂ = some m ∧ s ∈ to_list m) ↔
  (s ∈ to_list m₁ ∨ s ∈ to_list m₂) ∧ ∀ (a : α) (b₁ b₂ : β),
    sigma.mk a b₁ ∈ to_list m₁ → sigma.mk a b₂ ∈ to_list m₂ → b₁ = b₂)
(sdiff₂ [decidable_eq α] [decidable_eq β] : σ → σ → σ)
(mem_sdiff₂_iff [decidable_eq α] [decidable_eq β] : ∀ (m₁ m₂ : σ) (s : (Σ _ : α, β)),
  s ∈ to_list (sdiff₂ m₁ m₂) ↔ s ∈ to_list m₁ ∧ s ∉ to_list m₂)
(insert_with [decidable_eq α] :
  (β → β → β) → α → β → σ → σ)

namespace unordered_map
variables {α β σ : Type*} [unordered_map α β σ]
include β

def of_list [decidable_eq α] : list (Σ (_ : α), β) → σ
| []             := empty
| (⟨k, v⟩ :: xs) := kinsert k v (of_list xs)

lemma mem_of_lookup_is_some [decidable_eq α] {a : α} {m : σ} (h : (lookup a m).is_some) :
  sigma.mk a (option.get h) ∈ to_list m :=
by simp [← mem_lookup_iff]

def kerase_all [decidable_eq α] (m : σ) (as : list α) : σ :=
as.foldl kerase m

lemma mem_kerase_all_iff [decidable_eq α] (m : σ) (as : list α) (s : (Σ _ : α, β)) :
  s ∈ to_list (kerase_all m as) ↔ s.1 ∉ as ∧ s ∈ to_list m :=
begin
  revert m,
  simp only [kerase_all],
  induction as with a as ih,
  { simp },
  { intros m, simp only [list.foldl, list.mem_cons_iff],
    rw [ih, mem_kerase_iff],
    tauto }
end

lemma kerase_all_subset [decidable_eq α] (m : σ) (as : list α) :
  to_list (kerase_all m as) ⊆ to_list m :=
λ _, by { rw mem_kerase_all_iff, tauto }

lemma ksdiff_all_subset [decidable_eq α] (m₁ m₂ : σ) :
  to_list (ksdiff m₁ m₂) ⊆ to_list m₁ :=
λ _, by { rw mem_ksdiff_iff, tauto }

lemma subset_of_sdiff₂_null [decidable_eq α] [decidable_eq β] {m₁ m₂ : σ} :
  null (sdiff₂ m₁ m₂) →
  to_list m₁ ⊆ to_list m₂ :=
begin
  simp only [null_iff, list.eq_nil_iff_forall_not_mem, mem_sdiff₂_iff],
  intros h l, specialize h l,
  tauto
end

end unordered_map

universe u
open unordered_map

/-- Maps that can operate on any value type. -/
class generic_map (α : out_param Type*) (σ : Type u → Type u) :=
(to_map                : ∀ {β : Type u}, unordered_map α β (σ β))
(to_traversable        : traversable σ)
(to_lawful_traversable : is_lawful_traversable σ)
(filter_map          : ∀ {β₁ β₂ : Type u},
  (β₁ → option β₂) → σ β₁ → σ β₂)
(mem_filter_map_iff  : ∀ {β₁ β₂ : Type u} {f : β₁ → option β₂} {m₁ : σ β₁} {s : Σ (_ : α), β₂},
  s ∈ to_list (filter_map f m₁) ↔
  (∃ (b₁ : β₁),
    (⟨s.1, b₁⟩ : Σ (_ : α), β₁) ∈ to_list m₁ ∧
    f b₁ = some s.2))
(filter_map₂         : ∀ {β₁ β₂ β₃ : Type u},
  (β₁ → β₂ → option β₃) → σ β₁ → σ β₂ → option (σ β₃))
(mem_filter_map₂_iff : ∀ {β₁ β₂ β₃ : Type u} {f : β₁ → β₂ → option β₃} {m₁ : σ β₁} {m₂ : σ β₂} {s : Σ (_ : α), β₃},
  (∃ (m₃ : σ β₃), filter_map₂ f m₁ m₂ = some m₃ ∧ s ∈ to_list m₃) ↔
  (∃ (b₁ : β₁) (b₂ : β₂),
    (⟨s.1, b₁⟩ : Σ (_ : α), β₁) ∈ to_list m₁ ∧
    (⟨s.1, b₂⟩ : Σ (_ : α), β₂) ∈ to_list m₂ ∧
    f b₁ b₂ = some s.2) ∧
  (to_list m₁).keys ⊆ (to_list m₂).keys)

attribute [instance]
  generic_map.to_map
  generic_map.to_traversable
  generic_map.to_lawful_traversable
