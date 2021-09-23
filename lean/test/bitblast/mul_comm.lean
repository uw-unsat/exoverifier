/-
Copyright (c) 2021 The UNSAT Group. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luke Nelson, Xi Wang
-/
import aig.default
import aig.to_cnf
import sat.cnf
import sat.default
import sat.tactic
import smt.bitblast
import tactic.io

open sat.cnf
open sat.proof

section mul_commutativity

section
universe u
variables (n : ℕ) (β γ : Type u) [f : sat.factory β γ] [sat.var_factory β γ] [sat.any_factory β γ] [sat.const_factory β γ] [sat.and_factory β γ] [sat.iff_factory β γ] [sat.not_factory β γ] [sat.or_factory β γ]
include f

def mk_mul_comm_circuit (x y : fin n → bool) : state γ β := do
X : vector β n ← smt.bitblast.mk_var $ erased.mk x,
Y ← smt.bitblast.mk_var $ erased.mk y,
XY ← smt.bitblast.mk_mul X Y,
YX ← smt.bitblast.mk_mul Y X,
eq ← smt.bitblast.mk_eq XY YX,
sat.not_factory.mk_not eq.head

end

def bw : ℕ := string.to_nat (by tactic.io.from_env_var "BITWIDTH" "4")

@[reducible]
def zvec {n : ℕ} : fin n → bool := λ _, ff

def ff_circuit := ((mk_mul_comm_circuit bw aig.default.bref aig.default.factory zvec zvec).run aig.factory.init)

def ff_cnf' : option sat.cnf.default.formula := aig.ref.to_cnf ff_circuit.2.nodes ff_circuit.1.1

def ff_cnf : sat.cnf.default.formula := by {
  cases h : ff_cnf' with val,
  contradiction,
  from val }

def proof : sat.proof.default.proof :=
by semidecision.by_oracle aig.to_cnf_oracle (ff_circuit.2, (ff_circuit.1, ff))

lemma ff_cnf_unsatisfiable : unsatisfiable ff_cnf :=
semidec_trivial (decide_unsat_via_drup_check _ proof)

end mul_commutativity
