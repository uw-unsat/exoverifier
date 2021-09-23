/-
Copyright (c) 2021 The UNSAT Group. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luke Nelson, Xi Wang
-/
import aig.aiger
import aig.default
import aig.dot
import aig.to_cnf
import data.counter
import data.unordered_map.trie
import sat.default
import sat.factory
import sat.proof
import sat.tactic

open sat
open sat.cnf

namespace and4

section
universe u
variables {β γ : Type u} [f : sat.factory β γ] [sat.and_factory β γ]
include f

def mk_and4 (b₁ b₂ b₃ b₄ : β) : state γ β := do
b₅ ← sat.and_factory.mk_and b₁ b₂,
b₆ ← sat.and_factory.mk_and b₅ b₃,
sat.and_factory.mk_and b₆ b₄

def sat_mk_and4 (b₁ b₂ b₃ b₄ br : β) (r₁ r₂ r₃ r₄ : bool) (g g' : γ) :
  (mk_and4 b₁ b₂ b₃ b₄).run g = (br, g') →
  factory.sat g b₁ r₁ →
  factory.sat g b₂ r₂ →
  factory.sat g b₃ r₃ →
  factory.sat g b₄ r₄ →
  factory.sat g' br (r₁ && r₂ && r₃ && r₄) :=
begin
  intros mk sat1 sat2 sat3 sat4,
  simp only [mk_and4, state_t.run_bind] at mk,
  apply sat.and_factory.sat_mk_and mk,
  { apply and_factory.sat_mk_and,
    { simp only [prod.eq_iff_fst_eq_snd_eq]; tauto },
    { apply and_factory.sat_mk_and,
      { simp only [prod.eq_iff_fst_eq_snd_eq]; tauto },
      { from sat1 },
      { from sat2 } },
    { apply factory.sat_of_le,
      apply and_factory.le_mk_and,
      from sat3 } },
  { apply factory.sat_of_le,
    apply and_factory.le_mk_and,
    apply factory.sat_of_le,
    apply and_factory.le_mk_and,
    from sat4 }
end

end -- section

end and4

namespace and_comm

section
universe u
variables (β γ : Type u) [f : sat.factory β γ] [sat.var_factory β γ] [sat.and_factory β γ] [sat.iff_factory β γ] [sat.not_factory β γ]
include f

def mk_circuit (b₁ b₂ : bool) : state γ β := do
t₁ ← var_factory.mk_var $ erased.mk b₁,
t₂ ← var_factory.mk_var $ erased.mk b₂,
lhs ← and_factory.mk_and t₁ t₂,
rhs ← and_factory.mk_and t₂ t₁,
r ← iff_factory.mk_iff lhs rhs,
sat.not_factory.mk_not r

theorem sat_mk_circuit (b₁ b₂ : bool) (r : β) (g g' : γ) :
  (mk_circuit β γ b₁ b₂).run g = (r, g') →
  factory.sat g' r (!(biff (b₁ && b₂) (b₂ && b₁))) :=
begin
  intros mk,
  simp only [mk_circuit, state_t.run_bind] at mk,
  refine not_factory.sat_mk_not mk _,
  refine iff_factory.sat_mk_iff (by simp only [prod.mk.eta]) _ _,
  { refine factory.sat_of_le (by apply and_factory.le_mk_and) _,
    refine and_factory.sat_mk_and (by simp only [prod.mk.eta]) _ _,
    { refine factory.sat_of_le (by apply var_factory.le_mk_var) _,
      rw [← erased.out_mk b₁],
      refine var_factory.sat_mk_var (by simp only [erased.out_mk, prod.mk.eta]) },
    { rw [← erased.out_mk b₂],
      refine var_factory.sat_mk_var (by simp only [erased.out_mk, prod.mk.eta]) } },
  { refine and_factory.sat_mk_and (by simp only [prod.mk.eta]) _ _,
    { refine factory.sat_of_le (by apply and_factory.le_mk_and) _,
      rw [← erased.out_mk b₂],
      refine var_factory.sat_mk_var (by simp only [erased.out_mk, prod.mk.eta]) },
    { refine factory.sat_of_le (by apply and_factory.le_mk_and) _,
      refine factory.sat_of_le (by apply var_factory.le_mk_var) _,
      rw [← erased.out_mk b₁],
      refine var_factory.sat_mk_var (by simp only [erased.out_mk, prod.mk.eta]) } }
end

end -- section

def f_circuit : aig.default.bref × aig.default.factory :=
((mk_circuit _ _ ff ff).run aig.factory.init)

def proof : sat.proof.default.proof :=
by semidecision.by_oracle aig.to_cnf_oracle (f_circuit.2, (f_circuit.1, ff))

lemma helper (b : bool) :
  b = tt ↔ !b = ff := by cases b; tauto

theorem band_comm_tt_via_cnf (b₁ b₂ : bool) :
  biff (b₁ && b₂) (b₂ && b₁) = tt :=
begin
  rw helper,
  have sat₁ := sat_mk_circuit aig.default.bref aig.default.factory b₁ b₂ _ aig.factory.init _ (by rw [prod.mk.eta]),
  symmetry,
  revert sat₁,
  apply (aig.decide_via_to_cnf (_, (_, ff)) proof).of_as_true _,
  triv
end

end and_comm

namespace imp
variables (bp bq br bs bt : bool)

/-
<http://smtlib.cs.uiowa.edu/examples.shtml>

(set-logic QF_UF)
(declare-const p Bool) (declare-const q Bool) (declare-const r Bool)
(declare-const s Bool) (declare-const t Bool)
(assert (! (=> p q) :named PQ))
(assert (! (=> q r) :named QR))
(assert (! (=> r s) :named RS))
(assert (! (=> s t) :named ST))
(assert (! (not (=> q s)) :named NQS))
(check-sat)
-/

section
universe u
variables (β γ : Type u) [f : sat.factory β γ] [sat.var_factory β γ] [sat.all_factory β γ] [sat.implies_factory β γ] [sat.not_factory β γ]
include f

def mk_circuit : state γ β := do
p ← var_factory.mk_var $ erased.mk bp,
q ← var_factory.mk_var $ erased.mk bq,
r ← var_factory.mk_var $ erased.mk br,
s ← var_factory.mk_var $ erased.mk bs,
t ← var_factory.mk_var $ erased.mk bt,
pq ← implies_factory.mk_implies p q,
qr ← implies_factory.mk_implies q r,
rs ← implies_factory.mk_implies r s,
st ← implies_factory.mk_implies s t,
qs ← implies_factory.mk_implies q s,
nqs ← not_factory.mk_not qs,
all_factory.mk_all [pq, qr, rs, st, nqs]

end -- section

def f_circuit : aig.default.bref × aig.default.factory :=
((mk_circuit ff ff ff ff ff _ _).run aig.factory.init)

def f_cnf' : option default.formula := aig.ref.to_cnf f_circuit.2.nodes f_circuit.1.1

def f_cnf : default.formula := by {
  cases h : f_cnf' with val,
  contradiction,
  from val }

lemma f_cnf_unsatisfiable :
  unsatisfiable f_cnf :=
begin
  apply sat.proof.unsat_of_rup_check _ (by semidecision.by_oracle sat.proof.sat_oracle f_cnf) _,
  by refl
end

end imp
