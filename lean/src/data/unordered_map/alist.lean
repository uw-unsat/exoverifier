/-
Copyright (c) 2021 The UNSAT Group. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luke Nelson, Xi Wang
-/
import .basic
import data.list.alist

namespace alist
variables {α : Type*} {β : α → Type*}

/-- Return whether a map is empty. -/
def null (m : alist β) : bool :=
m.entries.empty

theorem null_iff (m : alist β) :
  m.null ↔ m.entries = [] :=
begin
  cases m with entries _,
  cases entries; simp [null, list.empty, has_emptyc.emptyc]
end

/-- Extract the element if the map is a singleton. -/
def unsingleton : alist β → option (Σ a : α, β a)
| ⟨[s], _⟩ := some s
| _        := none

theorem unsingleton_iff (m : alist β) (s : sigma β) :
  unsingleton m = some s ↔ m.entries = [s] :=
begin
  cases m with entries nodupkeys,
  cases entries with s₀ entries,
  { simp [unsingleton] },
  { cases entries with s₁ entries; simp [unsingleton] }
end

theorem mem_lookup_iff [decidable_eq α] (a : α) (b : β a) (m : alist β) :
  m.lookup a = some b ↔ sigma.mk a b ∈ m.entries :=
list.mem_lookup_iff m.nodupkeys

section kinsert
variable [decidable_eq α]

/-- Insert a key-value pair into a map if the key doesn't exist, or return the old map. -/
def kinsert (a : α) (b : β a) (m : alist β) : alist β :=
let r := lookup a m in
if hr : r.is_some then
  m
else
  ⟨⟨a, b⟩ :: m.entries, by {
    suffices : a ∉ m, by simpa [m.nodupkeys],
    rw ← lookup_eq_none,
    rwa option.not_is_some_iff_eq_none at hr }⟩

theorem mem_kinsert_iff (a : α) (b : β a) (m : alist β) (s : sigma β) :
  s ∈ (kinsert a b m).entries ↔
  (s ∈ m.entries ∨ (a ∉ m ∧ s = ⟨a, b⟩)) :=
begin
  simp only [kinsert],
  split_ifs with hr; rw lookup_is_some at hr,
  { tauto },
  { simp [hr, or_comm] }
end

end kinsert

section insert₂
variables [decidable_eq α] [∀ a, decidable_eq (β a)]

/--
Insert a key-value pair to a map. Return an empty map if a pair with the same key but a different
value exists in the map.
-/
def insert₂ (a : α) (b : β a) (m : alist β) : alist β :=
let r := lookup a m in
if hr : r.is_some then
  if b = option.get hr then
    m
  else
    ∅
else
  ⟨⟨a, b⟩ :: m.entries, by {
    suffices : a ∉ m, by simpa [m.nodupkeys],
    rw ← lookup_eq_none,
    rwa option.not_is_some_iff_eq_none at hr }⟩

theorem mem_insert₂_iff (a : α) (b : β a) (m : alist β) (s : sigma β) :
  s ∈ (insert₂ a b m).entries ↔
  (s = ⟨a, b⟩ ∨ s ∈ m.entries) ∧ (a ∈ m → sigma.mk a b ∈ m.entries) :=
begin
  simp only [insert₂],
  split_ifs with hr heq; rw lookup_is_some at hr,
  { -- ⟨a, b⟩ ∈ m: insert₂ a b m = m.
    have hab : sigma.mk a b ∈ m.entries,
    { rw ← mem_lookup_iff, finish },
    by_cases hs : s = ⟨a, b⟩;
    simp [hab, hr, hs] },
  { -- ⟨a, b'⟩ ∈ m where b ≠ b': insert₂ a b m = ∅.
    have hab : sigma.mk a b ∉ m.entries,
    { rw ← mem_lookup_iff, contrapose! heq, finish },
    tauto },
  { -- a ∉ m: insert₂ a b m = ⟨a, b⟩ :: m.
    simp [hr] }
end

lemma exists_of_insert₂_eq_nil {a : α} {b : β a} {m : alist β} :
  (insert₂ a b m).entries = [] →
  ∃ (b' : β a), sigma.mk a b' ∈ m.entries ∧ b ≠ b' :=
begin
  intro h,
  have h : ∀ s, s ∈ (insert₂ a b m).entries ↔ s ∈ [],
  { intro s, rw h },
  simp only [mem_insert₂_iff, list.not_mem_nil, iff_false,
             not_and, not_forall, exists_prop] at h,
  have h : a ∈ m ∧ sigma.mk a b ∉ m.entries,
  { apply h (sigma.mk a b), tauto },
  rcases h with ⟨ha, hab⟩,
  rcases list.exists_of_mem_keys ha with ⟨b', hb'⟩,
  existsi b',
  have hne : b ≠ b',
  { contrapose! hab, cc },
  tauto
end

lemma mem_of_insert₂_ne_nil {a : α} {b : β a} {m : alist β} :
  (insert₂ a b m).entries ≠ [] →
  a ∉ m ∨ sigma.mk a b ∈ m.entries :=
begin
  intro h,
  rw [← list.length_pos_iff_ne_nil, list.length_pos_iff_exists_mem] at h,
  rcases h with ⟨s, h⟩,
  rw mem_insert₂_iff at h,
  tauto
end

end insert₂

section union₂
variables [decidable_eq α] [∀ a, decidable_eq (β a)]

/--
Merge two maps. Return an empty map if they have a conflicting pair with the same key but
different values.
-/
def union₂ : alist β → alist β → option (alist β)
| ⟨[],      _⟩ := some
| ⟨s :: l₁, h⟩ := λ m₂, let m := insert₂ s.1 s.2 m₂ in
  if m.null then none else union₂ ⟨l₁, (list.nodupkeys_cons.1 h).2⟩ m

theorem mem_union₂_iff (m₁ m₂ : alist β) (s : sigma β) :
  (∃ (m : alist β), union₂ m₁ m₂ = some m ∧ s ∈ m.entries) ↔
  (s ∈ m₁.entries ∨ s ∈ m₂.entries) ∧
  (∀ {a : α} {b₁ b₂ : β a},
     sigma.mk a b₁ ∈ m₁.entries →
     sigma.mk a b₂ ∈ m₂.entries →
     b₁ = b₂) :=
begin
  revert m₂ s,
  cases m₁ with l₁ hl₁,
  induction l₁ with s₁ l₁ ih; intros, { simp [union₂] },
  simp only [union₂, list.mem_cons_iff],
  split_ifs with h₁; rw [null_iff] at h₁,
  { rcases exists_of_insert₂_eq_nil h₁ with ⟨b, h₂, h₃⟩,
    simp only [false_and, false_iff, exists_false],
    simp only [not_and, not_forall],
    intro h, clear h,
    existsi [s₁.1, s₁.2, b], simp [h₂, h₃] },
  { have h₂ := mem_of_insert₂_ne_nil h₁,
    rw [sigma.eta] at h₂,
    suffices : (∀ {a : α} {b₁ b₂ : β a},
                  sigma.mk a b₁ ∈ l₁ → sigma.mk a b₂ = s₁ ∨ sigma.mk a b₂ ∈ m₂.entries → b₁ = b₂) ↔
               (∀ {a : α} {b₁ b₂ : β a},
                  sigma.mk a b₁ = s₁ ∨ sigma.mk a b₁ ∈ l₁ → sigma.mk a b₂ ∈ m₂.entries → b₁ = b₂),
    { rw ih,
      simp only [mem_insert₂_iff, sigma.eta],
      cases h₂;
      { simp only [h₂, forall_false_left, implies_true_iff, and_true],
        conv_lhs { congr, rw [← or_assoc], congr, rw [or_comm] },
        rw [and.congr_right_iff], intro, assumption } },
    split,
    { rintro h₃ _ _ _ (h₄ | h₄) h₅,
      { cases h₄, cases h₂,
        { contrapose! h₂, exact list.mem_keys_of_mem h₅ },
        { apply list.nodupkeys.eq_of_mk_mem m₂.nodupkeys h₂ h₅ } },
      { apply h₃ h₄, right, exact h₅ } },
    { rintro h₃ _ _ _ h₄ (h₅ | h₅),
      { cases h₅, cases h₂,
        { have h := (list.nodupkeys_cons.1 hl₁).1, contrapose! h,
          exact list.mem_keys_of_mem h₄ },
        { apply h₃ _ h₂, right, exact h₄ } },
      { apply h₃ _ h₅, right, exact h₄ } } }
end

end union₂

section kerase
variable [decidable_eq α]

/-- A wrapper over `alist.erase`. -/
def kerase (m : alist β) (a : α) : alist β :=
erase a m

/-- This theorem is stronger than `alist.mem_erase`; the latter specifies only keys. -/
theorem mem_kerase_iff (m : alist β) (a : α) (s : sigma β) :
  s ∈ (kerase m a).entries ↔ s.1 ≠ a ∧ s ∈ m.entries :=
begin
  simp only [kerase, erase],
  split; intro h,
  { split,
    { have hkeys := list.mem_keys_of_mem h,
      rw [list.keys_kerase, list.mem_erase_iff_of_nodup m.nodupkeys] at hkeys,
      exact hkeys.1 },
    { apply list.mem_of_mem_erasep h } },
  { simp only [list.kerase],
    rw list.mem_erasep_of_neg; tauto }
end

end kerase

section erase₂
variables [decidable_eq α] [∀ a, decidable_eq (β a)]

/-- Remove a key-value pair from a map. -/
def erase₂ (m : alist β) (a : α) (b : β a) : alist β :=
⟨m.entries.erase ⟨a, b⟩, list.nodupkeys_of_sublist (by apply list.erase_sublist) m.nodupkeys⟩

theorem mem_erase₂_iff (m : alist β) (a : α) (b : β a) (s : sigma β) :
  s ∈ (erase₂ m a b).entries ↔ s ≠ ⟨a, b⟩ ∧ s ∈ m.entries :=
begin
  simp only [erase₂],
  cases decidable.em (s = ⟨a, b⟩) with h h,
  { suffices : sigma.mk a b ∉ m.entries.erase ⟨a, b⟩, by simpa [h],
    apply list.mem_erase_of_nodup,
    apply list.nodup_of_nodupkeys m.nodupkeys },
  { simp [h] }
end

end erase₂

section filter_map

/-- Combine filter and map. -/
def filter_map {γ : α → Type*} (f : ∀ {a : α}, β a → option (γ a)) (m : alist β) : alist γ :=
⟨m.entries.filter_map (λ s, sigma.mk s.1 <$> f s.2), by {
  have h := m.nodupkeys,
  rw [list.nodupkeys, list.keys, list.nodup] at h ⊢,
  rw [list.map_filter_map, list.pairwise_filter_map],
  rw [list.pairwise_map] at h,
  apply list.pairwise.imp _ h,
  simp only [option.mem_def, option.map_eq_map, option.map_eq_some'],
  simp only [and_imp, exists_imp_distrib, forall_apply_eq_imp_iff₂],
  tauto }⟩

theorem mem_filter_map_iff {γ : α → Type*} (f : ∀ {a : α}, β a → option (γ a)) (m : alist β)
                           (s : sigma γ) :
  s ∈ (filter_map @f m).entries ↔ ∃ b, (⟨s.1, b⟩ : sigma β) ∈ m.entries ∧ f b = some s.2 :=
begin
  rw [filter_map, list.mem_filter_map],
  simp only [option.map_eq_map, option.map_eq_some'],
  split,
  { rintro ⟨⟨a, b⟩, h₁, ⟨c, h₂, ⟨⟩⟩⟩,
    existsi b,
    simp [h₁, h₂] },
  { rintro ⟨b, h₁, h₂⟩,
    existsi (⟨s.1, b⟩ : sigma β),
    simp [h₁, h₂] }
end

end filter_map

section ksdiff
variables [decidable_eq α]

/-- Helper for `hsdiff`. -/
def ksdiff_aux : alist β → list α → alist β
| m []         := m
| m (hd :: tl) := ksdiff_aux (m.kerase hd) tl

/-- Remove pairs with keys in `m₂` from `m₁`. -/
def ksdiff (m₁ m₂ : alist β) : alist β :=
ksdiff_aux m₁ m₂.keys

lemma mem_ksdiff_aux_iff : ∀ (m : alist β) (l : list α) (s : sigma β),
  s ∈ (ksdiff_aux m l).entries ↔ s ∈ m.entries ∧ s.1 ∉ l
| m []         := by simp [ksdiff_aux]
| m (hd :: tl) := λ _, by {
  rw [ksdiff_aux, mem_ksdiff_aux_iff, mem_kerase_iff, list.mem_cons_iff],
  tauto }

theorem mem_ksdiff_iff (m₁ m₂ : alist β) (s : sigma β) :
  s ∈ (ksdiff m₁ m₂).entries ↔ s ∈ m₁.entries ∧ s.1 ∉ m₂.keys :=
by apply mem_ksdiff_aux_iff

end ksdiff

section sdiff₂
variables [decidable_eq α] [∀ a, decidable_eq (β a)]

/-- Remove key-value pairs in `m₂` from `m₁`. -/
def sdiff₂ (m₁ m₂ : alist β) : alist β :=
⟨m₁.entries.diff m₂.entries, list.nodupkeys_of_sublist (by apply list.diff_sublist) m₁.nodupkeys⟩

theorem mem_sdiff₂_iff (m₁ m₂ : alist β) (s : sigma β) :
  s ∈ (m₁.sdiff₂ m₂).entries ↔ s ∈ m₁.entries ∧ s ∉ m₂.entries :=
list.mem_diff_iff_of_nodup (list.nodup_of_nodupkeys m₁.nodupkeys)

theorem sdiff₂_eq_nil_iff_subset (m₁ m₂ : alist β) :
  (m₁.sdiff₂ m₂).entries = [] ↔ m₁.entries ⊆ m₂.entries :=
by simp [list.eq_nil_iff_forall_not_mem, list.subset_def, mem_sdiff₂_iff]

end sdiff₂

instance (α β : Type*) : unordered_map α β (alist (λ _ : α, β)) :=
{ to_list := alist.entries,
  nodupkeys := alist.nodupkeys,

  elems := λ m, m.entries.map (λ s, s.2),
  mem_elems_iff := by simp,

  empty := ∅,
  empty_eq := rfl,

  null := null,
  null_iff := null_iff,

  unsingleton := unsingleton,
  unsingleton_iff := unsingleton_iff,

  card := λ m, m.entries.length,
  card_eq := by cc,

  lookup := by apply lookup,
  mem_lookup_iff := by apply mem_lookup_iff,

  kinsert := by apply kinsert,
  mem_kinsert_iff := by apply mem_kinsert_iff,

  insert₂ := λ _ _, by exactI insert₂,
  mem_insert₂_iff := λ _ _, by apply mem_insert₂_iff,

  insert_with := λ _ _ _ _ _, ∅, -- TODO

  kerase := by apply kerase,
  mem_kerase_iff := by apply mem_kerase_iff,

  erase₂ := λ _ _, by exactI erase₂,
  mem_erase₂_iff := λ _ _, by apply mem_erase₂_iff,

  filter_map := λ f, filter_map (λ {_}, f),
  mem_filter_map_iff := λ f, mem_filter_map_iff (λ {_}, f),

  ksdiff := by apply ksdiff,
  mem_ksdiff_iff := by apply mem_ksdiff_iff,

  union₂ := λ _ _, by exactI union₂,
  mem_union₂_iff := λ _ _, by apply mem_union₂_iff,

  sdiff₂ := λ _ _, by exactI sdiff₂,
  mem_sdiff₂_iff := λ _ _, by apply mem_sdiff₂_iff }

end alist
