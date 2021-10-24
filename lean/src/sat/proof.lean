/-
Copyright (c) 2021 The UNSAT Group. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luke Nelson, Xi Wang
-/
import .cnf
import misc.semidecision

/-!
# SAT proof checking

This file provides support for checking clausal proofs produced by SAT solvers.

## References

* Marijn J.H. Heule and Armin Biere. *Proofs for Satisfiability Problems*, Chapter 1 of
  *All about Proofs, Proofs for All*.
  <https://www.cs.cmu.edu/~mheule/publications/APPA.pdf>

* Luís Cruz-Filipem, Marijn Heule, Warren Hunt, Matt Kaufmann, and Peter Schneider-Kamp.
  *Efficient Certified RAT Verification*.
  <https://imada.sdu.dk/~petersk/lrat/>
-/

namespace sat
namespace proof

open sat.cnf unordered_map semidecision

/-- Results of proof checking. -/
@[derive decidable_eq]
inductive result (κ : Type*)
| ok             : result
| out_of_hints   : result
| missing_clause : κ → result
| no_unit_clause : κ → result
| out_of_proof   : result
| no_rat_support : result
| missing_pivot  : result

namespace result
variable {κ : Type*}

instance : inhabited (result κ) :=
⟨result.ok⟩

section repr
variable [has_repr κ]

private def repr : result κ → string
| ok                 := "ok"
| out_of_hints       := "out of hints"
| (missing_clause k) := "missing clause " ++ has_repr.repr k
| (no_unit_clause k) := "no unit clause " ++ has_repr.repr k
| out_of_proof       := "out of proof"
| no_rat_support     := "no RAT support"
| missing_pivot      := "missing pivot"

instance : has_repr (result κ) :=
⟨repr⟩

end repr

end result

/-- A proof consists of a list of actions. Each action is of one of the following types:
* RUP addition:
  + a clause ID,
  + a clause (a set of literals), and
  + a list of clause IDs as hints for BCP.
* RAT addition:
  + a clause ID,
  + a pivot literal and clause (a set of literals),
  + an optional list of clause IDs, and
  + a list of pairs of a negated clause ID (containing the pivot) and clause IDs as hints for BCP.
* Deletion:
  + a set of clause IDs (a map from clause IDs to empty clauses).
-/
@[derive has_reflect]
inductive action (α β κ γ : Type*)
| rup : κ → β → list κ → action
| rat : κ → literal α → β → list κ → list (κ × list κ) → action
| del : κ → γ → action

/-- A DRUP is a list of actions. -/
abbreviation proof (α β κ γ : Type*) : Type* := list (action α β κ γ)

namespace action
variables {α β κ γ : Type*}

instance [inhabited κ] [inhabited γ] : inhabited (action α β κ γ) :=
⟨action.del (default κ) (default γ)⟩

section repr
variables [decidable_eq α] [has_coe_t α ℕ] [has_coe_t κ ℕ] [clause α β] [formula κ β γ]

private def has_repr_κ : has_repr κ :=
⟨λ k, repr (k : ℕ)⟩
local attribute [instance] has_repr_κ

private def lrat_aux : action α β κ γ → list string
| (rup k c hints)      := [repr k, clause.dimacs c] ++ hints.map repr
| (rat k l c ks hints) := [repr k, l.dimacs, clause.dimacs (kerase c l.1)] ++ ks.map repr ++
                           hints.bind (λ ⟨k, ks⟩, ("-" ++ repr k) :: ks.map repr)
| (del k f)            := [repr k, "d"] ++ (unordered_map.to_list f).keys.map repr

/-- Print an action in the LRAT format. -/
def lrat (a : action α β κ γ) : string :=
" ".intercalate (lrat_aux a ++ ["0"])

instance : has_repr (action α β κ γ) :=
⟨lrat⟩

end repr

end action

section action

section add
variables {α β κ γ : Type*} [clause α β] [formula κ β γ]
include α

/-- Adding a clause with RUP preserves logical equivalence. -/
def rup_spec (rup : γ → list κ → β → result κ) : Prop :=
∀ {f c hints}, rup f hints c = result.ok →
f ⇒ c

/-- Adding a clause with RAT preserves satisfiability. -/
def rat_spec [decidable_eq κ] (rat : γ → literal α → list κ → list (κ × list κ) → β → result κ) : Prop :=
∀ {f l c ks hints}, rat f l ks hints c = result.ok →
∀ k, unsatisfiable f ↔ unsatisfiable (kinsert k c f)

end add

section del
variables {β κ γ : Type*} [formula κ β γ]
include κ β

/-- Clause deletion is sound as it makes a clause easier to satisfy. -/
def del_spec (del : γ → γ → γ) : Prop :=
∀ f hints, to_list (del f hints) ⊆ to_list f

end del

end action

section refute
variables {α β κ γ : Type*} [clause α β] [formula κ β γ] [decidable_eq κ]

section
variables (rup : γ → list κ → β → result κ)
          (rat : γ → literal α → list κ → list (κ × list κ) → β → result κ)
          (del : γ → γ → γ)

/-- The proof checker is paramterized by handlers for types of actions. -/
def refute : γ → list (action α β κ γ) → result κ
| f []        := if (elems f).any null then result.ok else result.out_of_proof
| f (a :: as) := match a with
  | (action.rup k c hints)      := let r := rup f hints c in
    if r = result.ok then
      if as.empty ∧ null c then -- shortcut when c is both the last and empty
        result.ok
      else
        refute (kinsert k c f) as
    else
      r
  | (action.rat k l c ks hints) := let r := rat f l ks hints c in
    if r = result.ok then
      refute (kinsert k c f) as
    else
      r
  | (action.del _ hints)        := refute (del f hints) as
  end

end

theorem unsat_of_refute {rup} {rat} {del} (f : γ) (as : list (action α β κ γ)) :
  rup_spec rup →
  rat_spec rat →
  del_spec del →
  refute rup rat del f as = result.ok →
  unsatisfiable f :=
begin
  intros hrup hrat hdel,
  revert f,
  induction as with a as ih; intros f,
  { simp only [refute],
    split_ifs with h; try { tauto },
    intro hr,
    simp only [list.any_iff_exists] at h,
    rcases h with ⟨c, cf, h⟩,
    rw mem_elems_iff at cf,
    rcases cf with ⟨k, cf⟩,
    exact formula.unsat_of_unsat_of_mem cf (clause.unsat_of_null h) },
  { cases a; simp only [refute],
    case action.rup : k c hints {
      split_ifs with hr; intro hrefute,
      { cases h with _ h,
        apply limplies_unsat (hrup hr) (clause.unsat_of_null h) },
      { have ff' : f ⇒ kinsert k c f,
        { apply limplies_of_liff_left,
          apply formula.liff_kinsert_of_limplies,
          apply hrup hr },
        apply limplies_unsat ff' (ih _ hrefute) },
      { tauto } },
    case action.rat : k l c hints {
      split_ifs with hr; intro hrefute,
      { rw hrat hr k,
        apply ih _ hrefute },
      { tauto } },
    case action.del : k hints {
      intro hrefute,
      have ff' : f ⇒ del f hints,
      { apply formula.limplies_of_subset,
        apply hdel },
      apply limplies_unsat ff' (ih _ hrefute) } },
end

end refute

section rup
variables {α β κ γ : Type*} [clause α β] [formula κ β γ] [decidable_eq α] [decidable_eq κ]
include α

/-- Helper function for both `rup` and `rat`.

It returns either the checking status or the clause upon running out of hints; the latter is used
in RAT checking. -/
def rup_core (f : γ) : list κ → β → sum (result κ) β
| []        := sum.inr
| (k :: ks) := λ c, let cₖ := lookup k f in
  if hcₖ : cₖ.is_some then
    -- Compute c \ cₖ.
    let d := sdiff₂ (option.get hcₖ) c in
    -- If the result is an empty clause, succeed.
    if null d then
      sum.inl result.ok
    -- If the result is a unit clause l, continue with c ∪ {-l}.
    else
      let l := unsingleton d in
      -- Extract the literal from the unit clause.
      if hl : l.is_some then
        -- Compute c' = c ∪ {-l}.
        let nl := -option.get hl,
            c' := insert₂ nl.1 nl.2 c in
        -- There is no need to check whether c' is empty due to dual literals, since it doesn't
        -- affect the correctness of proof checking.
        rup_core ks c'
      -- If the result is neither empty nor a unit clause, the proof is invalid.
      else
        sum.inl $ result.no_unit_clause k
  -- If the clause ID doesn't exist, the proof is invalid.
  else
    sum.inl $ result.missing_clause k

/--
Check whether a clause has the RUP (reverse unit propagation) property with respect to a formula,
given a list of clause IDs as hints for BCP.

Clause c has the RUP property with respect to formula f if (f ∪ ¬c) causes a conflict via BCP,
meaning that f logically implies c. In other words, adding c to f preserves logical equivalence.
-/
def rup (f : γ) (hints : list κ) (c : β) : result κ :=
match rup_core f hints c with
| sum.inl r := r
| sum.inr _ := result.out_of_hints
end

theorem limplies_of_rup {f : γ} {c : β} {hints : list κ} :
  rup f hints c = result.ok →
  f ⇒ c :=
begin
  revert c,
  induction hints with k ks ih; try { tauto },
  intros c h,
  simp only [rup, rup_core] at h,
  split_ifs at h with hcₖ hd hl; try { tauto },

  -- cₖ \ c = ∅: show f ⇒ c from f ⇒ cₖ and cₖ ⇒ c.
  { have fcₖ : f ⇒ option.get hcₖ,
    { apply formula.limplies_of_lookup_is_some hcₖ },
    have cₖc : option.get hcₖ ⇒ c,
    { apply clause.limplies_of_subset,
      apply subset_of_sdiff₂_null hd },
    exact limplies.trans fcₖ cₖc },

  -- cₖ \ c = {l}: we have f ⇒ c ∪ {-l} from induction.
  { intros p pf,
    have pl : (p ⊭ option.get hl) ∨ (p ⊨ c),
    { rw ← literal.sat_neg_iff,
      apply clause.sat_or_sat_of_sat_of_limplies_insert₂ (ih h),
      assumption },
    -- Discharge the trivial case p ⊨ c.
    cases pl, swap, { assumption },

    -- Case p ⊭ l: given p ⊨ cₖ from p ⊨ f, there exists l' ∈ cₖ such that p ⊨ l', thus l' ≠ l.
    -- It suffices to show that l' ∈ c, which can be derived from cₖ \ c = {l}.
    have pcₖ : p ⊨ option.get hcₖ,
    { apply formula.limplies_of_lookup_is_some, assumption },
    simp only [clause.sat_iff_exists] at pcₖ,
    rcases pcₖ with ⟨l', l'cₖ, pl'⟩,

    have hne : l' ≠ option.get hl,
    { contrapose! pl, cases pl, exact pl' },

    suffices : l' ∈ to_list c,
    { apply clause.limplies_of_mem; assumption },

    suffices: l' ∉ to_list (sdiff₂ (option.get hcₖ) c),
    { have hsdiff := mem_sdiff₂_iff (option.get hcₖ) c l',
      tauto },

    have hsingleton : unsingleton (sdiff₂ (option.get hcₖ) c) = some (option.get hl),
    { simp },
    rw unsingleton_iff at hsingleton,
    rwa [hsingleton, list.mem_singleton] }
end

/-- A RUP checker. -/
def rup_check : γ → proof α β κ γ → result κ :=
refute rup (λ _ _ _ _ _, result.no_rat_support) (λ f _, f)

theorem unsat_of_rup_check (f : γ) (as : proof α β κ γ) :
  rup_check f as = result.ok → unsatisfiable f :=
unsat_of_refute f as (by apply limplies_of_rup) (by tauto) (by tauto)

/-- Decision procedure of unsatisfiability of a CNF via RUP checking. -/
def decide_unsat_via_rup_check : semidecision.procedure (unsatisfiable : set γ) (proof α β κ γ) :=
procedure.of_decidable_sound_relation (λ x w, rup_check x w = result.ok) unsat_of_rup_check

/-- A DRUP checker. -/
def drup_check : γ → proof α β κ γ → result κ :=
refute rup (λ _ _ _ _ _, result.no_rat_support) ksdiff

theorem unsat_of_drup_check (f : γ) (as : proof α β κ γ) :
drup_check f as = result.ok →
unsatisfiable f :=
unsat_of_refute f as (by apply limplies_of_rup) (by tauto) (by apply ksdiff_all_subset)

/-- Decision procedure of unsatisfiability of a CNF via DRUP checking. -/
def decide_unsat_via_drup_check : semidecision.procedure (unsatisfiable : set γ) (proof α β κ γ) :=
procedure.of_decidable_sound_relation (λ x w, drup_check x w = result.ok) unsat_of_drup_check

end rup

end proof
end sat
