/-
Copyright (c) 2021 The UNSAT Group. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luke Nelson, Xi Wang
-/
import .basic
import data.list.min_max
import data.unordered_map.trie

/-! CNF

This file provides basic support for formulas in conjunctive normal form (CNF).

## Implementation notes

This file defines type classes `clause` and `formula` as maps from variable IDs to bools and
from clause IDs to clauses, respectively. Both type classes are based on `unordered_map`.

## References

* <https://en.wikipedia.org/wiki/Conjunctive_normal_form>
-/

namespace sat
namespace cnf

/-- A literal consists of a variable and its sign (`tt` for ¬x, `ff` for x). -/
@[reducible]
def literal (α : Type*) :=
Σ _ : α, bool

/-- Typeclass for CNF clauses. -/
class clause (α : out_param Type*) (β : Type*) extends unordered_map α bool β

/-- Typeclass for CNF formulas. -/
class formula (κ β : out_param Type*) (γ : Type*) extends unordered_map κ β γ

namespace literal
variable {α : Type*}

/-- Print a literal. -/
def dimacs [has_coe_t α ℕ] (l : literal α) : string :=
cond l.2 "-" "" ++ repr (l.1 : ℕ)

instance : has_sat α (literal α) :=
⟨λ p l, bxor (p l.1) l.2⟩

/-- Create a literal. -/
@[reducible, simp]
protected def mk : α → bool → literal α :=
sigma.mk

/-- Create a positive literal. -/
@[reducible, simp]
protected def mk_pos (a : α) : literal α :=
literal.mk a ff

/-- Create a negative literal. -/
@[reducible, simp]
protected def mk_neg (a : α) : literal α :=
literal.mk a tt

meta instance (α : Type) [has_reflect α] [reflected α] : has_reflect (literal α)
| ⟨a, b⟩ := `(literal.mk a b : literal α)

lemma sat_iff (p : α → bool) (a : α) (b : bool) :
  p ⊨ literal.mk a b ↔ bxor (p a) b :=
by simp [has_sat.sat]

instance : has_neg (literal α) :=
⟨λ l, ⟨l.1, !l.2⟩⟩

@[simp]
lemma neg_neg (l : literal α) :
  -(-l) = l :=
by { cases l, simp [has_neg.neg] }

lemma sat_neg_iff (p : α → bool) (l : literal α) :
  p ⊨ -l ↔ p ⊭ l :=
begin
  cases l with a b,
  simp only [has_neg.neg, has_sat.sat],
  cases b; cases p a; dec_trivial
end

@[simp]
lemma not_sat_neg_iff (p : α → bool) (l : literal α) :
  p ⊭ -l ↔ p ⊨ l :=
by simp [sat_neg_iff]

end literal

namespace clause
variables {α β : Type*} [clause α β]

open unordered_map

/-- Print a clause. -/
def dimacs [has_coe_t α ℕ] (c : β) : string :=
string.join ((to_list c).map (λ l, literal.dimacs l ++ " ")) ++ "0"

@[priority 100] -- see Note [lower instance priority]
instance : has_sat α β :=
⟨λ p c, (to_list c).any (λ (l : literal α), p ⊨ l)⟩

lemma sat_iff_exists (p : α → bool) (c : β) :
  p ⊨ c ↔
  ∃ l ∈ to_list c, p ⊨ l :=
by simp [has_sat.sat, list.any_iff_exists]

section empty
include α

theorem unsat_empty :
  unsatisfiable (empty : β) :=
by { intro p, simp [sat_iff_exists, empty_eq] }

theorem unsat_of_null {c : β} :
  null c →
  unsatisfiable c :=
begin
  intros h p,
  rw null_iff at h,
  simp [sat_iff_exists, h]
end

end empty

section of_list
variable [decidable_eq α]

/-- Construct a clause from a list of literals. -/
def of_list (ls : list (literal α)) : β :=
ls.foldr (λ (l : literal α) c, kinsert l.1 l.2 c) empty

lemma mem_to_of_list_of_nodupkeys {ls : list (literal α)} (hnodupkeys : ls.nodupkeys) :
  ∀ (l : literal α), l ∈ to_list (of_list ls : β) ↔ l ∈ ls :=
begin
  induction ls with hd tl ih; intros l,
  { simp [of_list, empty_eq] },
  { rw list.nodupkeys_cons at hnodupkeys,
    rcases hnodupkeys with ⟨hmem, hnodupkeys⟩,
    specialize ih hnodupkeys,
    simp only [of_list, list.foldr] at ih ⊢,
    rw [mem_kinsert_iff, sigma.eta, ih, list.mem_cons_iff],
    split; intro h,
    { tauto },
    { cases h,
      { subst h,
        rw [eq_self_iff_true, and_true],
        right, contrapose! hmem,
        rw list.mem_keys at hmem,
        rcases hmem with ⟨b, hmem⟩,
        rw ih at hmem,
        apply list.mem_keys_of_mem hmem },
      { tauto } } }
end

lemma sat_of_list_of_nodupkeys (p : α → bool) {ls : list (literal α)} (h : ls.nodupkeys) :
  p ⊨ (of_list ls : β) ↔ ls.any (λ l, p ⊨ l) :=
begin
  simp only [sat_iff_exists, exists_prop, mem_to_of_list_of_nodupkeys h],
  simp [list.any_iff_exists]
end

end of_list

section mem

lemma liff_of_singleton (l : literal α) (c : β) :
  to_list c = [l] →
  l ⇔ c :=
begin
  intros hl p,
  rw [sat_iff_exists, hl],
  split; intro h,
  { existsi l, simp [h] },
  { rcases h with ⟨l', hl', pl'⟩,
    simp only [list.mem_singleton] at hl',
    subst l', assumption }
end

lemma limplies_of_mem {l : literal α} {c : β} :
  l ∈ to_list c →
  l ⇒ c :=
begin
  intros lc p pl,
  simp only [sat_iff_exists],
  tauto
end

lemma mem_of_limplies {l : literal α} {c : β} :
  l ⇒ c →
  l ∈ to_list c :=
begin
  classical,
  simp only [limplies, sat_iff_exists],
  intro h,
  cases l with a b,
  -- Construct an assignment p such that:
  --   a => !b
  --   x => y for any ⟨x, y⟩ ∈ c₂
  -- This ensures that p ⊨ ⟨a, b⟩ and p ⊭ c₂ \ {⟨a, b⟩}.
  let p := λ x, if x = a then !b else literal.mk_neg x ∈ to_list c,
  have hsat : p ⊨ literal.mk a b, by simp [p, has_sat.sat],
  specialize h p hsat,
  rcases h with ⟨⟨a', b'⟩, hmem', hsat'⟩,
  simp only [p, has_sat.sat] at hsat',
  split_ifs at hsat' with ha,
  { have hb : b = b', { cases b; cases b'; tauto },
    subst_vars, assumption },
  { cases b',
    { rw [bxor_ff, bool.of_to_bool_iff] at hsat',
      have h := list.nodupkeys.eq_of_mk_mem (nodupkeys c) hmem' hsat',
      tauto },
    { rw [bxor_tt, ← bool.to_bool_not, bool.of_to_bool_iff] at hsat',
      tauto } }
end

theorem limplies_iff_mem (l : literal α) (c : β) :
  l ⇒ c ↔
  l ∈ to_list c :=
iff.intro mem_of_limplies limplies_of_mem

end mem

section insert₂
variables {σ : Type*} [has_sat α σ]

lemma sat_or_sat_of_sat_of_limplies_insert₂ [decidable_eq α] {l : literal α} {c : β} {s : σ} :
  s ⇒ insert₂ l.1 l.2 c →
  ∀ (p : α → bool), p ⊨ s → (p ⊨ l) ∨ (p ⊨ c) :=
begin
  simp only [limplies],
  intros h p pf,
  specialize h p pf,
  simp only [clause.sat_iff_exists, mem_insert₂_iff, exists_prop] at h,
  rcases h with ⟨l', ⟨hl' | hl', hcons⟩, pl'⟩,
  { left, rw sigma.eta at hl', subst hl', assumption },
  { right, apply clause.limplies_of_mem hl', assumption }
end

end insert₂

section subset
include α

lemma limplies_of_subset {c₁ c₂ : β} :
  to_list c₁ ⊆ to_list c₂ →
  c₁ ⇒ c₂ :=
begin
  intros h p,
  simp only [sat_iff_exists],
  tauto
end

lemma subset_of_limplies {c₁ c₂ : β} :
  c₁ ⇒ c₂ →
  to_list c₁ ⊆ to_list c₂ :=
begin
  classical,
  simp only [limplies, sat_iff_exists],
  simp only [exists_prop, sigma.exists, exists_imp_distrib],
  rintros h ⟨a, b⟩ hmem,
  -- Construct an assignment p such that:
  --   a => !b
  --   x => y for any ⟨x, y⟩ ∈ c₂
  -- This ensures that p ⊨ ⟨a, b⟩ and p ⊭ c₂ \ {⟨a, b⟩}.
  let p := λ x, if x = a then !b else literal.mk_neg x ∈ to_list c₂,
  have hsat : p ⊨ literal.mk a b, by simp [p, has_sat.sat],
  specialize h p a b (and.intro hmem hsat),
  rcases h with ⟨a', b', hmem', hsat'⟩,
  simp only [p, has_sat.sat] at hsat',
  split_ifs at hsat' with ha,
  { -- This is the simple case: a = a' and b = b'.
    have hb : b = b', { cases b; cases b'; tauto },
    cc },
  { -- If a ≠ a', show a contradiction for either case of b'.
    cases b',
    { rw [bxor_ff, bool.of_to_bool_iff] at hsat',
      have h := list.nodupkeys.eq_of_mk_mem (nodupkeys c₂) hmem' hsat',
      tauto },
    { rw [bxor_tt, ← bool.to_bool_not, bool.of_to_bool_iff] at hsat',
      tauto } }
end

theorem limplies_iff_subset (c₁ c₂ : β) :
  c₁ ⇒ c₂ ↔
  to_list c₁ ⊆ to_list c₂ :=
iff.intro subset_of_limplies limplies_of_subset

theorem liff_ext (c₁ c₂ : β) :
  c₁ ⇔ c₂ ↔
  ∀ l, l ∈ to_list c₁ ↔ l ∈ to_list c₂ :=
begin
  rw liff_iff_limplies_and_limplies,
  simp only [limplies_iff_subset, list.subset_def, sigma.forall],
  split,
  { tauto },
  { intro h,
    split; intros a b hmem; specialize h a b; tauto }
end

end subset

end clause

namespace formula
variables {α β κ γ : Type*} [clause α β] [formula κ β γ]
open unordered_map

section dimacs
variables [has_coe_t α ℕ]
include α β κ

/-- Return the number of variables in a formula. -/
def nbvar (f : γ) : ℕ :=
let max : list ℕ → ℕ := λ ls, ls.maximum.get_or_else 0 in
max ((to_list f).map (λ s, max ((to_list s.2 : list (literal α)).keys.map coe)))

/-- Convert a formula to a string in the DIMACS format. -/
def dimacs [has_coe_t κ ℕ] (f : γ) : string :=
"p cnf " ++ repr (nbvar f) ++ " " ++ repr (card f) ++ "\n" ++
string.join (list.map (λ s, string.push s '\n') $
  ((to_list f).qsort (λ (s₁ s₂ : Σ _ : κ, β), (s₁.1 : ℕ) < (s₂.1 : ℕ)))
              .map (λ s, clause.dimacs s.2))

end dimacs

section sat
include β κ

@[nolint dangerous_instance, priority 100] -- see Note [lower instance priority]
instance : has_sat α γ :=
⟨λ p f, (to_list f).all (λ s, p ⊨ s.2)⟩

theorem sat_iff_forall (p : α → bool) (f : γ) :
  p ⊨ f ↔
  (∀ (k : κ) (c : β), sigma.mk k c ∈ to_list f → p ⊨ c) :=
by simp [has_sat.sat, list.all_iff_forall]

theorem sat_empty (p : α → bool) :
  p ⊨ (unordered_map.empty : γ) :=
by { simp [sat_iff_forall, empty_eq] }

section
include α

theorem unsat_of_unsat_of_mem {k : κ} {c : β} {f : γ} :
  sigma.mk k c ∈ to_list f →
  unsatisfiable c →
  unsatisfiable f :=
begin
  intros hmem hc p,
  simp only [sat_iff_forall, not_forall, exists_prop],
  existsi [k, c], tauto
end

end

end sat

section of_list
variables [decidable_eq κ] [has_one κ] [has_add κ]

/-- Construct a formula from a list of clauses. -/
def of_list (cs : list β) : γ :=
prod.fst $ cs.foldr (λ c (p : γ × κ), (kinsert p.2 c p.1, p.2 + 1)) (empty, 1)

/-- This lemma doesn't say that the result contains all clauses in the list (even though the
implementation does so). One advantage is that it doesn't depend on the properties of `κ`.
-/
lemma mem_to_of_list_of_mem {cs : list β} {k : κ} {c : β} :
  sigma.mk k c ∈ (to_list (of_list cs : γ)) →
  c ∈ cs :=
begin
  revert k c,
  induction cs with hd tl ih; intros k c,
  { simp [of_list, empty_eq] },
  { simp only [of_list, list.foldr],
    simp only [mem_kinsert_iff, list.mem_cons_iff, heq_iff_eq],
    tauto }
end

end of_list

section mem
include α β

theorem limplies_of_mem {k : κ} {c : β} {f : γ} :
  sigma.mk k c ∈ to_list f →
  f ⇒ c :=
begin
  intros h p pf,
  rw sat_iff_forall at pf,
  tauto
end

lemma limplies_of_lookup_is_some [decidable_eq κ] {k : κ} {f : γ} (h : (lookup k f).is_some) :
  f ⇒ option.get h :=
limplies_of_mem (mem_of_lookup_is_some h)

end mem

section subset
include α β κ

lemma limplies_of_subset {f₁ f₂ : γ} :
  to_list f₂ ⊆ to_list f₁ →
  f₁ ⇒ f₂ :=
begin
  intros h p,
  simp only [sat_iff_forall],
  tauto
end

lemma liff_kinsert_of_limplies [decidable_eq κ] (k : κ) {c : β} {f : γ} :
  f ⇒ c →
  f ⇔ kinsert k c f :=
begin
  simp only [limplies, liff],
  intros pc p,
  conv_rhs { simp only [sat_iff_forall, mem_kinsert_iff] },
  split,
  { rintros pf k' c' h,
    rcases h with h | ⟨h, hk, hc⟩,
    { apply limplies_of_mem h, assumption },
    { specialize pc _ pf, cc } },
  { rw sat_iff_forall,
    intros h k' c' h',
    apply h k' c', tauto }
end

end subset
end formula
end cnf
end sat
