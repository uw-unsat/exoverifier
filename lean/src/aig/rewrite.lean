/-
Copyright (c) 2021 The UNSAT Group. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luke Nelson, Xi Wang
-/
import .basic

/-!
# AIG rewriting

This file provides support for AIG rewriting using two-level optimization rules.

## Implementation notes

Optimization rules at level 1 are implemented by the factory.

Optimization rules at level 2, which return existing subterms (i.e., they don't create new terms),
are represented by `subrule`. These rules are confluent and terminating.

Optimization rules at level 3 & 4, which create new terms from existing subterms, are represented
by `newrule`. These rules require recursion.

## References

* Robert Brummayer and Armin Biere.
  *Local Two-Level And-Inverter Graph Minimization without Blowup*.
  <http://fmv.jku.at/papers/BrummayerBiere-MEMICS06.pdf>
-/

namespace aig
namespace rewrite

/-- A triple (node ID, edge, node) used by optimization rules. -/
@[reducible]
def term (α : Type*) : Type* :=
α × bool × node α

/-- An optimization rule at level 2, which returns an existing subterm. -/
structure subrule (α : Type*) :=
(run : term α → term α → option (ref α))
(sat : ∀ {r : ref α} {g : graph α} {a₁ a₂ : α} {b₁ b₂ r₁ r₂ : bool} {n₁ n₂ : node α},
  run (a₁, b₁, n₁) (a₂, b₂, n₂) = some r →
  g a₁ = some n₁ →
  g a₂ = some n₂ →
  (ref.root a₁ b₁).sat g r₁ →
  (ref.root a₂ b₂).sat g r₂ →
  r.sat g (r₁ && r₂))

namespace subrule
variable {α : Type*}

instance : inhabited (subrule α) :=
⟨{ run := λ _ _, none,
   sat := by tauto }⟩

/-- Flip a rule using commutativity. -/
def flip (o : subrule α) : subrule α :=
{ run := λ t₁ t₂, o.run t₂ t₁,
  sat := by {
    intros,
    rw bool.band_comm,
    apply o.sat; assumption } }

/-- Invoke a list of optimization rules and return the first successful result. -/
def optimize_with (t₁ t₂ : term α) : list (subrule α) → option (ref α)
| []        := none
| (f :: fs) := f.run t₁ t₂ <|> optimize_with fs

theorem sat_optimize {r : ref α} {g : graph α} {a₁ a₂ : α} {n₁ n₂ : node α}
                     {b₁ b₂ r₁ r₂ : bool} : ∀ {opts : list (subrule α)},
  optimize_with (a₁, b₁, n₁) (a₂, b₂, n₂) opts = some r →
  g a₁ = some n₁ →
  g a₂ = some n₂ →
  (ref.root a₁ b₁).sat g r₁ →
  (ref.root a₂ b₂).sat g r₂ →
  r.sat g (r₁ && r₂)
| []        := by tauto
| (f :: fs) := by {
  simp only [optimize_with],
  cases h : f.run (a₁, b₁, n₁) (a₂, b₂, n₂),
  { simp only [option.none_orelse],
    apply sat_optimize },
  { simp only [option.some_orelse],
    intro, subst_vars,
    apply subrule.sat; assumption } }

end subrule

private lemma ne_iff_eq_bnot (a b : bool) :
  a ≠ b ↔ a = !b :=
by cases a; cases b; dec_trivial

private lemma bnot_eq_iff_eq_bnot (a b : bool) :
  !a = b ↔ a = !b :=
by cases a; cases b; dec_trivial

section O2
variables {α : Type*} [decidable_eq α]

section contradiction_and_idempotence_2a

/-- Asymmetric rules of contradiction and idempotence:
* (a ∧ b) ∧ c -> ⊥,     if a = -c ∨ b = -c.
* (a ∧ b) ∧ c -> a ∧ b, if a =  c ∨ b =  c.
-/
private def run_contradiction_and_idempotence_2a : term α → term α → option (ref α)
| (a₁, ff, node.and a₁₁ b₁₁ a₁₂ b₁₂) (a₂, b₂, _) :=
  if a₁₁ = a₂ then
    some $ if b₁₁ = b₂ then ref.root a₁ ff else ref.bot
  else if a₁₂ = a₂ then
    some $ if b₁₂ = b₂ then ref.root a₁ ff else ref.bot
  else
    none
| _ _ := none

theorem sat_contradiction_and_idempotence_2a
  {r : ref α} {g : graph α} {a₁ a₂ : α} {b₁ b₂ r₁ r₂ : bool} {n₁ n₂ : node α} :
  run_contradiction_and_idempotence_2a (a₁, b₁, n₁) (a₂, b₂, n₂) = some r →
  g a₁ = some n₁ →
  g a₂ = some n₂ →
  (ref.root a₁ b₁).sat g r₁ →
  (ref.root a₂ b₂).sat g r₂ →
  r.sat g (r₁ && r₂) :=
begin
  cases b₁; try { tauto },
  cases n₁ with _ a₁₁ b₁₁ a₁₂ b₁₂; try { tauto },
  simp only [run_contradiction_and_idempotence_2a, ref.sat_root_iff, ff_bxor],
  intros h ga₁ ga₂ hsat₁ hsat₂,
  rw node.sat_and_iff ga₁ at hsat₁,
  rcases hsat₁ with ⟨r₁₁, r₁₂, hsat₁₁, hsat₁₂, hsat₁⟩,
  split_ifs at h with h₁ h₂ h₃ h₄; subst_vars,
  { have := node.sat_inj hsat₁₁ hsat₂, subst_vars,
    have := node.sat.and ga₁ hsat₁₁ hsat₁₂,
    rw [ref.sat_root_iff],
    cases r₂; simpa },
  { rw [← ne.def, ne_iff_eq_bnot] at h₂,
    have := node.sat_inj hsat₁₁ hsat₂,
    subst_vars,
    rw ref.sat_bot_iff,
    cases r₂; simp },
  { have := node.sat_inj hsat₁₂ hsat₂, subst_vars,
    have := node.sat.and ga₁ hsat₁₁ hsat₁₂,
    rw [ref.sat_root_iff],
    cases r₂; simpa },
  { rw [← ne.def, ne_iff_eq_bnot] at h₄,
    have := node.sat_inj hsat₁₂ hsat₂, subst_vars,
    rw ref.sat_bot_iff,
    cases r₂; simp },
  { exfalso, exact h }
end

private def contradiction_and_idempotence_2a : subrule α :=
{ run := run_contradiction_and_idempotence_2a,
  sat := by apply sat_contradiction_and_idempotence_2a }

end contradiction_and_idempotence_2a

section contradiction_2s

/-- Symmetric rule of contradiction:
* (a ∧ b) ∧ (c ∧ d) -> ⊥, if a = -c ∨ a = -d ∨ b = -c ∨ b = -d.

Don't use `flip` for commutativity.
-/
private def run_contradiction_2s : term α → term α → option (ref α)
| (_, ff, node.and a₁₁ b₁₁ a₁₂ b₁₂) (_, ff, node.and a₂₁ b₂₁ a₂₂ b₂₂) :=
  if b₁₁ ≠ b₂₁ ∧ a₁₁ = a₂₁ then
    some ref.bot
  else if b₁₁ ≠ b₂₂ ∧ a₁₁ = a₂₂ then
    some ref.bot
  else if b₁₂ ≠ b₂₁ ∧ a₁₂ = a₂₁ then
    some ref.bot
  else if b₁₂ ≠ b₂₂ ∧ a₁₂ = a₂₂ then
    some ref.bot
  else
    none
| _ _ := none

theorem sat_contradiction_2s
  {r : ref α} {g : graph α} {a₁ a₂ : α} {b₁ b₂ r₁ r₂ : bool} {n₁ n₂ : node α} :
  run_contradiction_2s (a₁, b₁, n₁) (a₂, b₂, n₂) = some r →
  g a₁ = some n₁ →
  g a₂ = some n₂ →
  (ref.root a₁ b₁).sat g r₁ →
  (ref.root a₂ b₂).sat g r₂ →
  r.sat g (r₁ && r₂) :=
begin
  cases b₁; try { tauto },
  cases n₁ with _ a₁₁ b₁₁ a₁₂ b₁₂; try { tauto },
  cases b₂; try { tauto },
  cases n₂ with _ a₂₁ b₂₁ a₂₂ b₂₂; try { tauto },
  simp only [run_contradiction_2s, ref.sat_root_iff, ff_bxor],
  intros h ga₁ ga₂ hsat₁ hsat₂,
  rw node.sat_and_iff ga₁ at hsat₁,
  rcases hsat₁ with ⟨r₁₁, r₁₂, hsat₁₁, hsat₁₂, hsat₁⟩,
  rw node.sat_and_iff ga₂ at hsat₂,
  rcases hsat₂ with ⟨r₂₁, r₂₂, hsat₂₁, hsat₂₂, hsat₂⟩,
  subst_vars,
  split_ifs at h with h₁ h₂ h₃ h₄; subst_vars; try { rw ref.sat_bot_iff },
  { simp only [ne_iff_eq_bnot] at h₁, cases h₁, subst_vars,
    have := node.sat_inj hsat₁₁ hsat₂₁, subst_vars,
    cases b₂₁; cases r₂₁; simp },
  { simp only [ne_iff_eq_bnot] at h₂, cases h₂, subst_vars,
    have := node.sat_inj hsat₁₁ hsat₂₂, subst_vars,
    cases b₂₂; cases r₂₂; simp },
  { simp only [ne_iff_eq_bnot] at h₃, cases h₃, subst_vars,
    have := node.sat_inj hsat₁₂ hsat₂₁, subst_vars,
    cases b₂₁; cases r₂₁; simp },
  { simp only [ne_iff_eq_bnot] at h₄, cases h₄, subst_vars,
    have := node.sat_inj hsat₁₂ hsat₂₂, subst_vars,
    cases b₂₂; cases r₂₂; simp },
  { exfalso, exact h }
end

private def contradiction_2s : subrule α :=
{ run := run_contradiction_2s,
  sat := by apply sat_contradiction_2s }

end contradiction_2s

section subsumption_2a

/-- Asymmetric rule of subsumption:
* ¬(a ∧ b) ∧ c -> c, if a = -c ∨ b = -c.
-/
private def run_subsumption_2a : term α → term α → option (ref α)
| (_, tt, node.and a₁₁ b₁₁ a₁₂ b₁₂) (a₂, b₂, _) :=
  if b₁₁ ≠ b₂ ∧ a₁₁ = a₂ then
    some $ ref.root a₂ b₂
  else if b₁₂ ≠ b₂ ∧ a₁₂ = a₂ then
    some $ ref.root a₂ b₂
  else
    none
| _ _ := none

theorem sat_subsumption_2a
  {r : ref α} {g : graph α} {a₁ a₂ : α} {b₁ b₂ r₁ r₂ : bool} {n₁ n₂ : node α} :
  run_subsumption_2a (a₁, b₁, n₁) (a₂, b₂, n₂) = some r →
  g a₁ = some n₁ →
  g a₂ = some n₂ →
  (ref.root a₁ b₁).sat g r₁ →
  (ref.root a₂ b₂).sat g r₂ →
  r.sat g (r₁ && r₂) :=
begin
  cases b₁; try { tauto },
  cases n₁ with _ a₁₁ b₁₁ a₁₂ b₁₂; try { tauto },
  simp only [run_subsumption_2a, ref.sat_root_iff, tt_bxor],
  intros h ga₁ ga₂ hsat₁ hsat₂,
  rw node.sat_and_iff ga₁ at hsat₁,
  rcases hsat₁ with ⟨r₁₁, r₁₂, hsat₁₁, hsat₁₂, hsat₁⟩,
  simp only [ne_iff_eq_bnot] at h,
  simp only [bnot_eq_iff_eq_bnot] at hsat₁,
  split_ifs at h with h₁ h₂; subst_vars; rw [ref.sat_root_iff] <|> tauto,
  { cases h₁, subst_vars,
    have := node.sat_inj hsat₁₁ hsat₂, subst_vars,
    cases r₂; simpa using hsat₂ },
  { cases h₂, subst_vars,
    have := node.sat_inj hsat₁₂ hsat₂, subst_vars,
    cases r₂; simpa using hsat₂ },
end

private def subsumption_2a : subrule α :=
{ run := run_subsumption_2a,
  sat := by apply sat_subsumption_2a }

end subsumption_2a

section subsumption_2s

/-- Symmetric rule of contradiction:
* ¬(a ∧ b) ∧ (c ∧ d) -> c ∧ d, if a = -c ∨ a = -d ∨ b = -c ∨ b = -d.
-/
private def run_subsumption_2s : term α → term α → option (ref α)
| (_, tt, node.and a₁₁ b₁₁ a₁₂ b₁₂) (a₂, ff, node.and a₂₁ b₂₁ a₂₂ b₂₂) :=
  if b₁₁ ≠ b₂₁ ∧ a₁₁ = a₂₁ then
    some $ ref.root a₂ ff
  else if b₁₁ ≠ b₂₂ ∧ a₁₁ = a₂₂ then
    some $ ref.root a₂ ff
  else if b₁₂ ≠ b₂₁ ∧ a₁₂ = a₂₁ then
    some $ ref.root a₂ ff
  else if b₁₂ ≠ b₂₂ ∧ a₁₂ = a₂₂ then
    some $ ref.root a₂ ff
  else
    none
| _ _ := none

theorem sat_subsumption_2s
  {r : ref α} {g : graph α} {a₁ a₂ : α} {b₁ b₂ r₁ r₂ : bool} {n₁ n₂ : node α} :
  run_subsumption_2s (a₁, b₁, n₁) (a₂, b₂, n₂) = some r →
  g a₁ = some n₁ →
  g a₂ = some n₂ →
  (ref.root a₁ b₁).sat g r₁ →
  (ref.root a₂ b₂).sat g r₂ →
  r.sat g (r₁ && r₂) :=
begin
  cases b₁; try { tauto },
  cases n₁ with _ a₁₁ b₁₁ a₁₂ b₁₂; try { tauto },
  cases b₂; try { tauto },
  cases n₂ with _ a₂₁ b₂₁ a₂₂ b₂₂; try { tauto },
  simp only [run_subsumption_2s, ref.sat_root_iff, ff_bxor, tt_bxor],
  intros h ga₁ ga₂ hsat₁ hsat₂,
  rw node.sat_and_iff ga₁ at hsat₁,
  rcases hsat₁ with ⟨r₁₁, r₁₂, hsat₁₁, hsat₁₂, hsat₁⟩,
  rw bnot_eq_iff_eq_bnot at hsat₁,
  rw node.sat_and_iff ga₂ at hsat₂,
  rcases hsat₂ with ⟨r₂₁, r₂₂, hsat₂₁, hsat₂₂, hsat₂⟩,
  subst_vars,
  have := node.sat.and ga₂ hsat₂₁ hsat₂₂,
  simp only [← ne.def, ne_iff_eq_bnot] at h,
  split_ifs at h with h₁ h₂ h₃ h₄; subst_vars; try { rw [ref.sat_root_iff, ff_bxor] },
  { cases h₁, subst_vars,
    have := node.sat_inj hsat₁₁ hsat₂₁, subst_vars,
    cases b₂₁; cases r₂₁; simpa },
  { cases h₂, subst_vars,
    have := node.sat_inj hsat₁₁ hsat₂₂, subst_vars,
    cases b₂₂; cases r₂₂; simpa },
  { cases h₃, subst_vars,
    have := node.sat_inj hsat₁₂ hsat₂₁, subst_vars,
    cases b₂₁; cases r₂₁; simpa },
  { cases h₄, subst_vars,
    have := node.sat_inj hsat₁₂ hsat₂₂, subst_vars,
    cases b₂₂; cases r₂₂; simpa },
  { exfalso, exact h }
end

private def subsumption_2s : subrule α :=
{ run := run_subsumption_2s,
  sat := by apply sat_subsumption_2s }

end subsumption_2s

section resolution

/-- Rule of resolution:
* ¬(a ∧ b) ∧ ¬(c ∧ d) -> ¬a, if (a = c ∧ b = -d) ∨ (a = d ∧ b = -c).

Don't use `flip` for commutativity.
-/
private def run_resolution : term α → term α → option (ref α)
| (_, tt, node.and a₁₁ b₁₁ a₁₂ b₁₂) (_, tt, node.and a₂₁ b₂₁ a₂₂ b₂₂) :=
  if b₁₁ = b₂₁ ∧ b₁₂ ≠ b₂₂ ∧ a₁₁ = a₂₁ ∧ a₁₂ = a₂₂ then
    some $ ref.root a₁₁ (!b₁₁)
  else if b₁₁ = b₂₂ ∧ b₁₂ ≠ b₂₁ ∧ a₁₁ = a₂₂ ∧ a₁₂ = a₂₁ then
    some $ ref.root a₁₁ (!b₁₁)
  else if b₁₂ = b₂₁ ∧ b₁₁ ≠ b₂₂ ∧ a₁₂ = a₂₁ ∧ a₁₁ = a₂₂ then
    some $ ref.root a₁₂ (!b₁₂)
  else if b₁₂ = b₂₂ ∧ b₁₁ ≠ b₂₁ ∧ a₁₂ = a₂₂ ∧ a₁₁ = a₂₁ then
    some $ ref.root a₁₂ (!b₁₂)
  else
    none
| _ _ := none

theorem sat_resolution
  {r : ref α} {g : graph α} {a₁ a₂ : α} {b₁ b₂ r₁ r₂ : bool} {n₁ n₂ : node α} :
  run_resolution (a₁, b₁, n₁) (a₂, b₂, n₂) = some r →
  g a₁ = some n₁ →
  g a₂ = some n₂ →
  (ref.root a₁ b₁).sat g r₁ →
  (ref.root a₂ b₂).sat g r₂ →
  r.sat g (r₁ && r₂) :=
begin
  cases b₁; try { tauto },
  cases n₁ with _ a₁₁ b₁₁ a₁₂ b₁₂; try { tauto },
  cases b₂; try { tauto },
  cases n₂ with _ a₂₁ b₂₁ a₂₂ b₂₂; try { tauto },
  simp only [run_resolution, ref.sat_root_iff, tt_bxor],
  intros h ga₁ ga₂ hsat₁ hsat₂,
  rw node.sat_and_iff ga₁ at hsat₁,
  rcases hsat₁ with ⟨r₁₁, r₁₂, hsat₁₁, hsat₁₂, hsat₁⟩,
  rw node.sat_and_iff ga₂ at hsat₂,
  rcases hsat₂ with ⟨r₂₁, r₂₂, hsat₂₁, hsat₂₂, hsat₂⟩,
  rw bnot_eq_iff_eq_bnot at hsat₁ hsat₂,
  subst_vars,
  simp only [← ne.def, ne_iff_eq_bnot] at h,
  split_ifs at h with h₁ h₂ h₃ h₄,
  { rcases h₁ with ⟨_, _, _, _⟩, subst_vars,
    have := node.sat_inj hsat₁₁ hsat₂₁,
    have := node.sat_inj hsat₁₂ hsat₂₂,
    subst_vars,
    rw ref.sat_root_iff,
    cases b₂₂; cases r₂₂; simpa },
  { rcases h₂ with ⟨_, _, _, _⟩, subst_vars,
    have := node.sat_inj hsat₁₁ hsat₂₂,
    have := node.sat_inj hsat₁₂ hsat₂₁,
    subst_vars,
    rw ref.sat_root_iff,
    cases b₂₁; cases r₂₁; simpa },
  { rcases h₃ with ⟨_, _, _, _⟩, subst_vars,
    have := node.sat_inj hsat₁₁ hsat₂₂,
    have := node.sat_inj hsat₁₂ hsat₂₁,
    subst_vars,
    rw ref.sat_root_iff,
    cases b₂₂; cases r₂₂; simpa },
  { rcases h₄ with ⟨_, _, _, _⟩, subst_vars,
    have := node.sat_inj hsat₁₁ hsat₂₁,
    have := node.sat_inj hsat₁₂ hsat₂₂,
    subst_vars,
    rw ref.sat_root_iff,
    cases b₂₁; cases r₂₁; simpa },
  { exfalso, exact h }
end

private def resolution : subrule α :=
{ run := run_resolution,
  sat := by apply sat_resolution }

end resolution

end O2

/-- An optimization rule at level 3 or 4, which returns a pair of terms for creating a new term. -/
structure newrule (α : Type*) :=
(run : term α → term α → graph α → option (term α × term α))
(sat : ∀ {g : graph α} {a₁ a₂ a₁' a₂' : α} {b₁ b₂ b₁' b₂' r₁ r₂ : bool} {n₁ n₂ n₁' n₂' : node α},
  run (a₁, b₁, n₁) (a₂, b₂, n₂) g = some ((a₁', b₁', n₁'), (a₂', b₂', n₂')) →
  g a₁ = some n₁ →
  g a₂ = some n₂ →
  (ref.root a₁ b₁).sat g r₁ →
  (ref.root a₂ b₂).sat g r₂ →
  g a₁' = some n₁' ∧
  g a₂' = some n₂' ∧
  ∃ (r₁' r₂' : bool),
    (ref.root a₁' b₁').sat g r₁' ∧
    (ref.root a₂' b₂').sat g r₂' ∧
    r₁ && r₂ = r₁' && r₂')

namespace newrule
variable {α : Type*}

instance : inhabited (newrule α) :=
⟨{ run := λ _ _ _, none,
   sat := by tauto }⟩

/-- Flip a rule using commutativity. -/
def flip (o : newrule α) : newrule α :=
{ run := λ t₁ t₂ g, o.run t₂ t₁ g,
  sat := by {
    intros,
    rw bool.band_comm,
    apply o.sat; assumption } }

/-- Invoke a list of optimization rules and return the first successful result. -/
def optimize_with (t₁ t₂ : term α) (g : graph α) : list (newrule α) → option (term α × term α)
| []        := none
| (f :: fs) := f.run t₁ t₂ g <|> optimize_with fs

theorem sat_optimize {g : graph α} {a₁ a₂ a₁' a₂' : α} {b₁ b₂ b₁' b₂' r₁ r₂ : bool}
                     {n₁ n₂ n₁' n₂' : node α} : ∀ {opts : list (newrule α)},
  optimize_with (a₁, b₁, n₁) (a₂, b₂, n₂) g opts = some ((a₁', b₁', n₁'), (a₂', b₂', n₂')) →
  g a₁ = some n₁ →
  g a₂ = some n₂ →
  (ref.root a₁ b₁).sat g r₁ →
  (ref.root a₂ b₂).sat g r₂ →
  g a₁' = some n₁' ∧
  g a₂' = some n₂' ∧
  ∃ (r₁' r₂' : bool),
    (ref.root a₁' b₁').sat g r₁' ∧
    (ref.root a₂' b₂').sat g r₂' ∧
    r₁ && r₂ = r₁' && r₂'
| []        := by tauto
| (f :: fs) := by {
  simp only [optimize_with],
  cases h : f.run (a₁, b₁, n₁) (a₂, b₂, n₂) g,
  { simp only [option.none_orelse],
    apply sat_optimize },
  { simp only [option.some_orelse],
    intro, subst_vars,
    apply newrule.sat; assumption } }

end newrule

section O3
variables {α : Type*} [decidable_eq α]

section substitution_3a

/-- Asymmetric rule of substitution:
* ¬(a ∧ b) ∧ c -> ¬a ∧ b, if b = c.
-/
private def run_substitution_3a : term α → term α → graph α → option (term α × term α)
| (_, tt, node.and a₁₁ b₁₁ a₁₂ b₁₂) (a₂, b₂, n₂) g :=
  if b₁₂ = b₂ ∧ a₁₂ = a₂ then do
    n₁₁ ← g a₁₁,
    some ((a₁₁, !b₁₁, n₁₁), (a₂, b₂, n₂))
  else if b₁₁ = b₂ ∧ a₁₁ = a₂ then do
    n₁₂ ← g a₁₂,
    some ((a₁₂, !b₁₂, n₁₂), (a₂, b₂, n₂))
  else
    none
| _ _ _ := none

theorem sat_substitution_3a
  {g : graph α} {a₁ a₂ a₁' a₂' : α} {b₁ b₂ b₁' b₂' r₁ r₂ : bool} {n₁ n₂ n₁' n₂' : node α} :
  run_substitution_3a (a₁, b₁, n₁) (a₂, b₂, n₂) g = some ((a₁', b₁', n₁'), (a₂', b₂', n₂')) →
  g a₁ = some n₁ →
  g a₂ = some n₂ →
  (ref.root a₁ b₁).sat g r₁ →
  (ref.root a₂ b₂).sat g r₂ →
  g a₁' = some n₁' ∧
  g a₂' = some n₂' ∧
  ∃ (r₁' r₂' : bool),
    (ref.root a₁' b₁').sat g r₁' ∧
    (ref.root a₂' b₂').sat g r₂' ∧
    r₁ && r₂ = r₁' && r₂' :=
begin
  cases b₁; try { tauto },
  cases n₁ with _ a₁₁ b₁₁ a₁₂ b₁₂; try { tauto },
  simp only [run_substitution_3a, ref.sat_root_iff, tt_bxor],
  intros h ga₁ ga₂ hsat₁ hsat₂,
  rw node.sat_and_iff ga₁ at hsat₁,
  rcases hsat₁ with ⟨r₁₁, r₁₂, hsat₁₁, hsat₁₂, hsat₁⟩,
  simp only [bnot_eq_iff_eq_bnot] at hsat₁,
  subst_vars,
  split_ifs at h with h₁ h₂,
  { cases h₁, subst_vars,
    simp only [option.bind_eq_some, prod.mk.inj_iff] at h,
    rcases h with ⟨n₁₁, ga₁₁, ⟨_, _, _⟩, ⟨_, _, _⟩⟩, subst_vars,
    have := node.sat_inj hsat₁₂ hsat₂, subst_vars,
    simp only [ga₁₁, ga₂, eq_self_iff_true, true_and],
    existsi [bxor (!b₁₁) r₁₁, r₂],
    simp only [bxor_invol],
    simp only [hsat₁₁, hsat₁₂, true_and],
    cases b₁₁; cases r₂; simp },
  { cases h₂, subst_vars,
    simp only [option.bind_eq_some, prod.mk.inj_iff] at h,
    rcases h with ⟨n₁₂, ga₁₂, ⟨_, _, _⟩, ⟨_, _, _⟩⟩, subst_vars,
    have := node.sat_inj hsat₁₁ hsat₂, subst_vars,
    simp only [ga₁₂, ga₂, eq_self_iff_true, true_and],
    existsi [bxor (!b₁₂) r₁₂, r₂],
    simp only [bxor_invol],
    simp only [hsat₁₁, hsat₁₂, true_and],
    cases b₁₂; cases r₂; simp },
  { exfalso, exact h },
end

private def substitution_3a : newrule α :=
{ run := run_substitution_3a,
  sat := by apply sat_substitution_3a }

end substitution_3a

section substitution_3s

/-- Symmetric rule of substitution:
* ¬(a ∧ b) ∧ (c ∧ d) -> ¬a ∧ (c ∧ d), if b = c ∨ b = d.
-/
private def run_substitution_3s : term α → term α → graph α → option (term α × term α)
| (_, tt, node.and a₁₁ b₁₁ a₁₂ b₁₂) (a₂, ff, node.and a₂₁ b₂₁ a₂₂ b₂₂) g :=
  if (b₁₂ = b₂₁ ∧ a₁₂ = a₂₁) ∨ (b₁₂ = b₂₂ ∧ a₁₂ = a₂₂) then do
    n₁₁ ← g a₁₁,
    some ((a₁₁, !b₁₁, n₁₁), (a₂, ff, node.and a₂₁ b₂₁ a₂₂ b₂₂))
  else if (b₁₁ = b₂₁ ∧ a₁₁ = a₂₁) ∨ (b₁₁ = b₂₂ ∧ a₁₁ = a₂₂) then do
    n₁₂ ← g a₁₂,
    some ((a₁₂, !b₁₂, n₁₂), (a₂, ff, node.and a₂₁ b₂₁ a₂₂ b₂₂))
  else
    none
| _ _ _ := none

theorem sat_substitution_3s
  {g : graph α} {a₁ a₂ a₁' a₂' : α} {b₁ b₂ b₁' b₂' r₁ r₂ : bool} {n₁ n₂ n₁' n₂' : node α} :
  run_substitution_3s (a₁, b₁, n₁) (a₂, b₂, n₂) g = some ((a₁', b₁', n₁'), (a₂', b₂', n₂')) →
  g a₁ = some n₁ →
  g a₂ = some n₂ →
  (ref.root a₁ b₁).sat g r₁ →
  (ref.root a₂ b₂).sat g r₂ →
  g a₁' = some n₁' ∧
  g a₂' = some n₂' ∧
  ∃ (r₁' r₂' : bool),
    (ref.root a₁' b₁').sat g r₁' ∧
    (ref.root a₂' b₂').sat g r₂' ∧
    r₁ && r₂ = r₁' && r₂' :=
begin
  cases b₁; try { tauto },
  cases n₁ with _ a₁₁ b₁₁ a₁₂ b₁₂; try { tauto },
  cases b₂; try { tauto },
  cases n₂ with _ a₂₁ b₂₁ a₂₂ b₂₂; try { tauto },
  simp only [run_substitution_3s, ref.sat_root_iff, ff_bxor, tt_bxor],
  intros h ga₁ ga₂ hsat₁ hsat₂,
  rw node.sat_and_iff ga₁ at hsat₁,
  rcases hsat₁ with ⟨r₁₁, r₁₂, hsat₁₁, hsat₁₂, hsat₁⟩,
  simp only [bnot_eq_iff_eq_bnot] at hsat₁,
  rw node.sat_and_iff ga₂ at hsat₂,
  rcases hsat₂ with ⟨r₂₁, r₂₂, hsat₂₁, hsat₂₂, hsat₂⟩,
  subst_vars,
  split_ifs at h with h₁ h₂,
  { simp only [option.bind_eq_some, prod.mk.inj_iff] at h,
    rcases h with ⟨n₁₁, ga₁₁, ⟨_, _, _⟩, ⟨_, _, _⟩⟩, subst_vars,
    simp only [ga₁₁, ga₂, eq_self_iff_true, true_and, ff_bxor],
    cases h₁; cases h₁; subst_vars,
    { have := node.sat_inj hsat₁₂ hsat₂₁, subst_vars,
      have hsat₂ := node.sat.and ga₂ hsat₂₁ hsat₂₂,
      existsi [bxor (!b₁₁) r₁₁, bxor b₂₁ r₂₁ && bxor b₂₂ r₂₂],
      simp only [bxor_invol, hsat₁₁, hsat₂, true_and],
      cases bxor b₂₁ r₂₁; cases b₁₁; simp },
    { have := node.sat_inj hsat₁₂ hsat₂₂, subst_vars,
      have hsat₂ := node.sat.and ga₂ hsat₂₁ hsat₂₂,
      existsi [bxor (!b₁₁) r₁₁, bxor b₂₁ r₂₁ && bxor b₂₂ r₂₂],
      simp only [bxor_invol, hsat₁₁, hsat₂, true_and],
      cases bxor b₂₂ r₂₂; cases b₁₁; simp } },
  { simp only [option.bind_eq_some, prod.mk.inj_iff] at h,
    rcases h with ⟨n₁₂, ga₁₂, ⟨_, _, _⟩, ⟨_, _, _⟩⟩, subst_vars,
    simp only [ga₁₂, ga₂, eq_self_iff_true, true_and, ff_bxor],
    cases h₂; cases h₂; subst_vars,
    { have := node.sat_inj hsat₁₁ hsat₂₁, subst_vars,
      have hsat₂ := node.sat.and ga₂ hsat₂₁ hsat₂₂,
      existsi [bxor (!b₁₂) r₁₂, bxor b₂₁ r₂₁ && bxor b₂₂ r₂₂],
      simp only [bxor_invol, hsat₁₂, hsat₂, true_and],
      cases bxor b₂₁ r₂₁; cases b₁₂; simp },
    { have := node.sat_inj hsat₁₁ hsat₂₂, subst_vars,
      have hsat₂ := node.sat.and ga₂ hsat₂₁ hsat₂₂,
      existsi [bxor (!b₁₂) r₁₂, bxor b₂₁ r₂₁ && bxor b₂₂ r₂₂],
      simp only [bxor_invol, hsat₁₂, hsat₂, true_and],
      cases bxor b₂₂ r₂₂; cases b₁₂; simp } },
  { exfalso, exact h },
end

private def substitution_3s : newrule α :=
{ run := run_substitution_3s,
  sat := by apply sat_substitution_3s }

end substitution_3s

end O3

section O4
variables {α : Type*} [decidable_eq α]

section idempotence_4s

/-- Symmetric rule of idempotence:
* (a ∧ b) ∧ (c ∧ d) -> (a ∧ b) ∧ d, if a = c ∨ b = c.
* (a ∧ b) ∧ (c ∧ d) -> (a ∧ b) ∧ c, if a = d ∨ b = d.

O4 rules are not confluent, as they could perform the following rewrites instead:
* (a ∧ b) ∧ (c ∧ d) -> a ∧ (c ∧ d), if b = c ∨ b = d.
* (a ∧ b) ∧ (c ∧ d) -> b ∧ (c ∧ d), if a = c ∨ a = d.

Don't use `flip` for commutativity.
-/
private def run_idempotence_4s : term α → term α → graph α → option (term α × term α)
| (a₁, ff, node.and a₁₁ b₁₁ a₁₂ b₁₂) (_, ff, node.and a₂₁ b₂₁ a₂₂ b₂₂) g :=
  if (b₁₁ = b₂₁ ∧ a₁₁ = a₂₁) ∨ (b₁₂ = b₂₁ ∧ a₁₂ = a₂₁) then do
    n₂₂ ← g a₂₂,
    some ((a₁, ff, node.and a₁₁ b₁₁ a₁₂ b₁₂), (a₂₂, b₂₂, n₂₂))
  else if (b₁₁ = b₂₂ ∧ a₁₁ = a₂₂) ∨ (b₁₂ = b₂₂ ∧ a₁₂ = a₂₂) then do
    n₂₁ ← g a₂₁,
    some ((a₁, ff, node.and a₁₁ b₁₁ a₁₂ b₁₂), (a₂₁, b₂₁, n₂₁))
  else
    none
| _ _ _ := none

theorem sat_idempotence_4s
  {g : graph α} {a₁ a₂ a₁' a₂' : α} {b₁ b₂ b₁' b₂' r₁ r₂ : bool} {n₁ n₂ n₁' n₂' : node α} :
  run_idempotence_4s (a₁, b₁, n₁) (a₂, b₂, n₂) g = some ((a₁', b₁', n₁'), (a₂', b₂', n₂')) →
  g a₁ = some n₁ →
  g a₂ = some n₂ →
  (ref.root a₁ b₁).sat g r₁ →
  (ref.root a₂ b₂).sat g r₂ →
  g a₁' = some n₁' ∧
  g a₂' = some n₂' ∧
  ∃ (r₁' r₂' : bool),
    (ref.root a₁' b₁').sat g r₁' ∧
    (ref.root a₂' b₂').sat g r₂' ∧
    r₁ && r₂ = r₁' && r₂' :=
begin
  cases b₁; try { tauto },
  cases n₁ with _ a₁₁ b₁₁ a₁₂ b₁₂; try { tauto },
  cases b₂; try { tauto },
  cases n₂ with _ a₂₁ b₂₁ a₂₂ b₂₂; try { tauto },
  simp only [run_idempotence_4s, ref.sat_root_iff, ff_bxor],
  intros h ga₁ ga₂ hsat₁ hsat₂,
  rw node.sat_and_iff ga₁ at hsat₁,
  rcases hsat₁ with ⟨r₁₁, r₁₂, hsat₁₁, hsat₁₂, hsat₁⟩,
  rw node.sat_and_iff ga₂ at hsat₂,
  rcases hsat₂ with ⟨r₂₁, r₂₂, hsat₂₁, hsat₂₂, hsat₂⟩,
  subst_vars,
  split_ifs at h with h₁ h₂; try { exfalso, exact h };
  simp only [option.bind_eq_some, prod.mk.inj_iff] at h,
  { rcases h with ⟨n₂₂, ga₂₂, ⟨_, _, _⟩, ⟨_, _, _⟩⟩, subst_vars,
    simp only [ga₁, ga₂₂, eq_self_iff_true, true_and, ff_bxor],
    cases h₁; cases h₁; subst_vars,
    { have := node.sat_inj hsat₁₁ hsat₂₁, subst_vars,
      have hsat₁ := node.sat.and ga₁ hsat₂₁ hsat₁₂,
      existsi [bxor b₂₁ r₂₁ && bxor b₁₂ r₁₂, bxor b₂₂ r₂₂],
      simp only [bxor_invol, hsat₁, hsat₂₂, true_and],
      cases bxor b₂₁ r₂₁; simp },
    { have := node.sat_inj hsat₁₂ hsat₂₁, subst_vars,
      have hsat₁ := node.sat.and ga₁ hsat₁₁ hsat₂₁,
      existsi [bxor b₁₁ r₁₁ && bxor b₂₁ r₂₁, bxor b₂₂ r₂₂],
      simp only [bxor_invol, hsat₁, hsat₂₂, true_and],
      cases bxor b₂₁ r₂₁; simp } },
  { rcases h with ⟨n₂₁, ga₂₁, ⟨_, _, _⟩, ⟨_, _, _⟩⟩, subst_vars,
    simp only [ga₁, ga₂₁, eq_self_iff_true, true_and, ff_bxor],
    cases h₂; cases h₂; subst_vars,
    { have := node.sat_inj hsat₁₁ hsat₂₂, subst_vars,
      have hsat₁ := node.sat.and ga₁ hsat₂₂ hsat₁₂,
      existsi [bxor b₂₂ r₂₂ && bxor b₁₂ r₁₂, bxor b₂₁ r₂₁],
      simp only [bxor_invol, hsat₁, hsat₂₁, true_and],
      cases bxor b₂₂ r₂₂; simp },
    { have := node.sat_inj hsat₁₂ hsat₂₂, subst_vars,
      have hsat₁ := node.sat.and ga₁ hsat₁₁ hsat₂₂,
      existsi [bxor b₁₁ r₁₁ && bxor b₂₂ r₂₂, bxor b₂₁ r₂₁],
      simp only [bxor_invol, hsat₁, hsat₂₁, true_and],
      cases bxor b₂₂ r₂₂; simp } },
end

private def idempotence_4s : newrule α :=
{ run := run_idempotence_4s,
  sat := by apply sat_idempotence_4s }

end idempotence_4s

end O4

/-- The result of AIG optimizations is either a subterm or two terms for creating a new term. -/
inductive result (α : Type*)
| sub : ref α → result
| new : term α → term α → result

namespace result
variable {α : Type*}

instance : inhabited (result α) :=
⟨sub (default : (ref α))⟩

end result

section interface
variables {α : Type*} [decidable_eq α]

/-- Optimization rules at level 2. -/
def subrules : list (subrule α) :=
[ contradiction_and_idempotence_2a,
  contradiction_and_idempotence_2a.flip,
  contradiction_2s, -- no flip
  subsumption_2a,
  subsumption_2a.flip,
  subsumption_2s,
  subsumption_2s.flip,
  resolution ]      -- no flip

/-- Optimization rules at level 3 or 4. -/
def newrules : list (newrule α) :=
[ idempotence_4s,   -- no flip
  -- Run O4 rules before O3 rules; the latter assume the children of the top node are normalized.
  substitution_3a,
  substitution_3a.flip,
  substitution_3s,
  substitution_3s.flip ]

/-- Run AIG optimizations with a given depth. -/
def optimize_with (g : graph α) : ℕ → term α → term α → result α
| 0       t₁ t₂ := result.new t₁ t₂
| (n + 1) t₁ t₂ := match subrule.optimize_with t₁ t₂ subrules with
  | some r := result.sub r                       -- first run optimizations at level 2
  | none   := match newrule.optimize_with t₁ t₂ g newrules with
    | some (t₁', t₂') := optimize_with n t₁' t₂' -- recurse for optimizations at level 3/4
    | none            := result.new t₁ t₂        -- use input if no optimizations apply
    end
  end

/-- The depth for running optimizations. Setting to 0 disables two-level optimization rules. -/
def depth : ℕ :=
1

/-- Run AIG optimizations. -/
@[reducible]
def optimize (g : graph α) : term α → term α → result α :=
optimize_with g depth

theorem sat_optimize {n : ℕ} {res : result α} {g : graph α} {a₁ a₂ : α} {b₁ b₂ r₁ r₂ : bool} {n₁ n₂ : node α} :
  optimize_with g n (a₁, b₁, n₁) (a₂, b₂, n₂) = res →
  g a₁ = some n₁ →
  g a₂ = some n₂ →
  (ref.root a₁ b₁).sat g r₁ →
  (ref.root a₂ b₂).sat g r₂ →
  (∀ {r : ref α},
     res = result.sub r →
     r.sat g (r₁ && r₂)) ∧
  (∀ {a₁' a₂' : α} {b₁' b₂' : bool} {n₁' n₂' : node α},
     res = result.new (a₁', b₁', n₁') (a₂', b₂', n₂') →
     g a₁' = some n₁' ∧
     g a₂' = some n₂' ∧
     ∃ (r₁' r₂' : bool),
       (ref.root a₁' b₁').sat g r₁' ∧
       (ref.root a₂' b₂').sat g r₂' ∧
       r₁ && r₂ = r₁' && r₂') :=
begin
  revert res a₁ b₁ n₁ a₂ b₂ n₂ r₁ r₂,
  induction n with n ih; intros _ _ _ _ _ _ _ _ _ h ga₁ ga₂ hsat₁ hsat₂,
  { simp only [optimize_with] at h, subst_vars,
    simp only [forall_false_left, forall_const, true_and, prod.mk.inj_iff],
    rintro _ _ _ _ _ _ ⟨⟨_, _, _⟩, ⟨_, _, _⟩⟩, subst_vars,
    tauto },
  { cases h₁ : subrule.optimize_with (a₁, b₁, n₁) (a₂, b₂, n₂) subrules,
    { cases h₂ : newrule.optimize_with (a₁, b₁, n₁) (a₂, b₂, n₂) g newrules with t,
      { simp only [optimize_with, h₁, h₂] at h, subst_vars,
        simp only [forall_false_left, forall_const, true_and, prod.mk.inj_iff],
        rintro _ _ _ _ _ _ ⟨⟨_, _, _⟩, ⟨_, _, _⟩⟩, subst_vars,
        tauto },
      { rcases t with ⟨⟨a₁', b₁', n₁'⟩, ⟨a₂', b₂', n₂'⟩⟩,
        simp only [optimize_with, h₁, h₂] at h,
        rcases newrule.sat_optimize h₂ ga₁ ga₂ hsat₁ hsat₂ with
               ⟨ga₁', ga₂', ⟨_, _, hsat₁', hsat₂', heq⟩⟩,
        specialize ih h ga₁' ga₂' hsat₁' hsat₂',
        rw heq, assumption } },
    { simp only [optimize_with, h₁] at h, subst_vars,
      have hsat := subrule.sat_optimize h₁ ga₁ ga₂ hsat₁ hsat₂,
      simp only [forall_false_left, forall_eq'], tauto } }
end

end interface

end rewrite
end aig
