/-
Copyright (c) 2021 The UNSAT Group. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luke Nelson, Xi Wang
-/
import .cnf
import misc.option
import misc.semidecision

/-!
# DPLL

This is an implementation of the Davis-Putnam-Logemann-Loveland (DPLL) algorithm.

## Implementation notes

* This DPLL implementation is for testing purposes only and is thus not optimized for performance.
  We intend to run an external SAT solver and validate its proof, rather than running SAT solving
  directly in the Lean kernel.

* An earlier implementation of BCP used well-founded recursion. As both newer versions of Lean 3
  and Lean 4 change the computational behavior and cause it to not compute anymore, we change BCP
  to using a fuel.

## References

* <https://en.wikipedia.org/wiki/DPLL_algorithm>
-/

open sat.cnf
open unordered_map

namespace sat
variables {α β : Type*} [clause α β]

namespace list_formula
include α

instance : has_sat α (list β) :=
⟨λ p f, f.all (λ c, p ⊨ c)⟩

theorem sat_iff_forall (p : α → bool) (f : list β) :
  p ⊨ f ↔
  (∀ (c : β), c ∈ f → p ⊨ c) :=
by simp [has_sat.sat, list.all_iff_forall]

theorem limplies_of_mem {c : β} {f : list β} :
  c ∈ f →
  f ⇒ c :=
begin
  intros lc p pf,
  rw [sat_iff_forall] at pf,
  exact pf _ lc
end

theorem limplies_of_subset {f₁ f₂ : list β} :
  f₁ ⊆ f₂ →
  f₂ ⇒ f₁ :=
begin
  simp only [limplies, sat_iff_forall],
  tauto
end

theorem unsat_of_unsat_of_mem {c : β} {f : list β} :
  c ∈ f →
  unsatisfiable c →
  unsatisfiable f :=
begin
  intros cf hc p,
  rw [unsatisfiable] at hc,
  rw [sat_iff_forall, not_forall],
  existsi c, tauto
end

theorem sat_map_iff_sat {p : α → bool} {g : β → β} (hg : ∀ c, p ⊨ g c ↔ p ⊨ c) {f : list β} :
  p ⊨ (f.map (λ c, g c)) ↔ p ⊨ f :=
begin
  simp only [sat_iff_forall, list.mem_map],
  simp only [exists_imp_distrib, and_imp],
  rw [forall_apply_eq_imp_iff₂],
  split; intros h c hc,
  { rw ← hg,
    apply h, assumption },
  { specialize h c hc,
    specialize hg c,
    tauto }
end

theorem sat_filter_iff_sat {p : α → bool} {g : β → Prop} [decidable_pred g]
                           (hg : ∀ c, ¬ g c → p ⊨ c) {f : list β} :
  p ⊨ (f.filter g) ↔ p ⊨ f :=
begin
  split; intro h,
  { rw [sat_iff_forall] at h ⊢,
    intros c hmem,
    { cases decidable.em (g c) with hdec hdec,
    { apply h,
      apply list.mem_filter_of_mem hmem hdec },
    { apply hg _ hdec } } },
  { apply limplies_of_subset (f.filter_subset),
    assumption }
end

end list_formula

namespace dpll

/-- Find a unit clause in a given formula. -/
def find_unit_clause (f : list β) : option (literal α) :=
f.mfirst unsingleton

theorem mem_of_find_unit_clause {f : list β} {l : literal α} :
  find_unit_clause f = some l →
  ∃ c, c ∈ f ∧ to_list c = [l] :=
begin
  simp only [find_unit_clause],
  induction f with c f ih, { tauto },
  simp only [list.mfirst, list.mem_cons_iff],
  intro h,
  cases hc : unsingleton c with l',
  { rw [hc, option.none_orelse] at h,
    specialize ih h,
    cases ih with c' ih,
    existsi c', tauto },
  { simp only [hc, option.some_orelse] at h,
    subst l',
    rw [unsingleton_iff] at hc,
    existsi c, simp [hc] }
end

section bcp
variable [decidable_eq α]
include α

/-- Perform BCP on a given literal:
* remove clauses that contain `l`; and
* remove `-l` from each clause.
-/
def bcp_on (l : literal α) (f : list β) : list β :=
(f.filter (λ c, lookup l.1 c ≠ some l.2)).map (λ c, erase₂ c l.1 (!l.2))

theorem sat_bcp_on_iff_sat {p : α → bool} {l : literal α} (pl : p ⊨ l) (f : list β) :
  p ⊨ bcp_on l f ↔ p ⊨ f :=
begin
  simp only [bcp_on],
  transitivity (p ⊨ f.filter (λ c, lookup l.1 c ≠ some l.2)),
  { apply list_formula.sat_map_iff_sat,
    intro c,
    simp only [clause.sat_iff_exists],
    split,
    { rintro ⟨l', h, pl'⟩,
      simp only [mem_erase₂_iff] at h,
      tauto },
    { rintro ⟨l', l'c, pl'⟩,
      existsi l',
      simp only [pl', l'c, exists_prop, and_true, mem_erase₂_iff],
      have hl : (⟨l.fst, !l.snd⟩ : literal α) = -l, by refl,
      rw hl, clear hl,
      contrapose! pl', subst pl',
      simpa } },
  { apply list_formula.sat_filter_iff_sat,
    intros c lc,
    rw [not_not, ← option.mem_def, mem_lookup_iff] at lc,
    rw [clause.sat_iff_exists],
    existsi l, cases l, simp [lc, pl] }
end

theorem limplies_bcp_on_of_limplies {l : literal α} {f : list β} (h : f ⇒ l) :
  f ⇒ bcp_on l f :=
begin
  intros p pf,
  rwa sat_bcp_on_iff_sat,
  apply h, assumption
end

theorem limplies_bcp_on_of_unit_clause {l : literal α} {f : list β} (h : ∃ c, c ∈ f ∧ to_list c = [l]) :
  f ⇒ bcp_on l f :=
begin
  apply limplies_bcp_on_of_limplies,
  rcases h with ⟨c, cf, hc⟩,
  have fc := list_formula.limplies_of_mem cf,
  have cl := limplies_of_liff_right (clause.liff_of_singleton l c hc),
  exact limplies.trans fc cl
end

/-- Perform BCP for a given formula. -/
def bcp : ℕ → list β → list β
| 0       := id
| (n + 1) := λ f, match find_unit_clause f with
  | none   := f
  | some l := bcp n (bcp_on l f)
  end

theorem limplies_bcp_of_unit_clause (n : ℕ) (f : list β) :
  f ⇒ bcp n f :=
begin
  revert f,
  induction n with n ih; intro f, { refl },
  cases hfind : find_unit_clause f with l,
  { simp [hfind, bcp] },
  { simp only [hfind, bcp],
    transitivity bcp_on l f,
    { apply limplies_bcp_on_of_unit_clause (mem_of_find_unit_clause hfind) },
    { apply ih } }
end

end bcp

/-- Choose the first literal of the first clause. -/
def choose_literal {f : list β} (h₁ : ¬ f.empty) (h₂ : ¬ (f.find (λ c, null c)).is_some) : literal α :=
let c : β := f.nth_le 0 (by {
  rw [list.empty_iff_eq_nil] at h₁,
  exact list.length_pos_of_ne_nil h₁ }) in
(to_list c).nth_le 0 (by {
  rw [option.not_is_some_iff_eq_none, list.find_eq_none] at h₂,
  simp only [null_iff] at h₂,
  specialize h₂ c (list.nth_le_mem _ _ _),
  exact list.length_pos_of_ne_nil h₂ })

section
variable [decidable_eq α]
include α

/-- The core DPLL algorithm. -/
def dpll_core : ℕ → list β → option unit
| 0       := λ _, some ()
| (n + 1) := λ f, let g := bcp n f in
  if h₁ : g.empty then
    some ()
  else if h₂ : (g.find (λ c, null c)).is_some then
    none
  else
    let l := choose_literal h₁ h₂ in
    dpll_core n (bcp_on l g) <|> dpll_core n (bcp_on (-l) g)

theorem unsat_of_dpll_aux_eq_none {n : ℕ} {f : list β} :
  dpll_core n f = none →
  unsatisfiable f :=
begin
  revert f,
  induction n with n ih, { tauto },
  simp only [dpll_core],
  intros f h,
  apply limplies_unsat (limplies_bcp_of_unit_clause n f),
  split_ifs at h with h₁ h₂,
  { tauto },
  { rw [option.is_some_iff_exists] at h₂,
    cases h₂ with c h₂,
    apply list_formula.unsat_of_unsat_of_mem (list.find_mem h₂),
    apply clause.unsat_of_null,
    apply list.find_some h₂ },
  { simp only [option.orelse_eq_none_iff] at h,
    have hpos := ih h.1,
    have hneg := ih h.2,
    intro p,
    cases decidable.em (p ⊨ choose_literal h₁ h₂) with pa pa,
    { contrapose! hpos,
      rw [← sat_bcp_on_iff_sat pa] at hpos,
      tauto },
    { rw [← literal.sat_neg_iff] at pa,
      contrapose! hneg,
      rw [← sat_bcp_on_iff_sat pa] at hneg,
      tauto } }
end

end -- section
end dpll

section
variables {κ γ : Type*} [formula κ β γ] [decidable_eq α]
include α β κ

/-- Perform SAT solving using the DPLL algorithm. -/
def dpll (f : γ) : option unit :=
let cs := elems f in
dpll.dpll_core (cs.map card).sum cs

theorem unsat_of_dpll_eq_none {f : γ} :
  dpll f = none →
  unsatisfiable f :=
begin
  intro h,
  have hunsat := dpll.unsat_of_dpll_aux_eq_none h,
  simp only [unsatisfiable] at hunsat ⊢,
  simp only [formula.sat_iff_forall],
  simp only [list_formula.sat_iff_forall] at hunsat,
  intro p,
  specialize hunsat p,
  simp only [not_forall, exists_prop] at hunsat ⊢,
  simp only [mem_elems_iff] at hunsat,
  rcases hunsat with ⟨c, ⟨k, hmem⟩, pc⟩,
  existsi [k, c, hmem],
  exact pc
end

/-- Semidecidability of a CNF via DPLL. -/
def decide_unsat_via_dpll {ω : Type*} : semidecision.procedure (unsatisfiable : set γ) ω :=
semidecision.procedure.of_decidable_sound_relation (λ f _, dpll f = none) (λ _ _, unsat_of_dpll_eq_none)

end -- section
end sat
