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

open sat.cnf sat.proof

section and_commutativity

section
universe u
variables (n : ℕ) (β γ : Type u) [f : sat.factory β γ] [sat.var_factory β γ] [sat.any_factory β γ] [sat.const_factory β γ] [sat.and_factory β γ] [sat.iff_factory β γ] [sat.not_factory β γ] [sat.or_factory β γ]
include f

def mk_add_comm_circuit (x y : fin n → bool) : state γ β := do
X ← smt.bitblast.mk_var $ erased.mk x,
Y ← smt.bitblast.mk_var $ erased.mk y,
XY ← smt.bitblast.mk_add X Y,
YX ← smt.bitblast.mk_add Y X,
eq ← smt.bitblast.mk_eq XY.1 YX.1,
sat.not_factory.mk_not eq.head

end

def bw : ℕ := string.to_nat (by tactic.io.from_env_var "BITWIDTH" "8")

@[reducible]
def zvec {n : ℕ} : fin n → bool := λ _, ff

def ff_circuit := ((mk_add_comm_circuit bw aig.default.bref aig.default.factory zvec zvec).run aig.factory.init)

def ff_cnf' : option sat.cnf.default.formula := aig.ref.to_cnf ff_circuit.2.nodes ff_circuit.1.1

def ff_cnf : sat.cnf.default.formula := by {
  cases h : ff_cnf' with val,
  contradiction,
  from val }

def proof : sat.proof.default.proof :=
by semidecision.by_oracle aig.to_cnf_oracle (ff_circuit.2, (ff_circuit.1, ff))

lemma ff_cnf_unsatisfiable :
  unsatisfiable ff_cnf :=
semidec_trivial (decide_unsat_via_drup_check _ proof)

end and_commutativity

-- section add_associativity

-- section
-- universe u
-- variables (n : ℕ) (β γ : Type u) [f : sat.factory β γ] [sat.var_factory β γ] [sat.any_factory β γ] [sat.const_factory β γ] [sat.and_factory β γ] [sat.iff_factory β γ] [sat.not_factory β γ]
-- include f

-- def mk_add_assoc_circuit (x y z : fin n → bool) : state γ β := do
--   X ← smt.bitblast.mk_var $ vector.of_fn x,
--   Y ← smt.bitblast.mk_var $ vector.of_fn y,
--   Z ← smt.bitblast.mk_var $ vector.of_fn z,
--   XY ← smt.bitblast.mk_add X Y,
--   YZ ← smt.bitblast.mk_add Y Z,
--   XY_Z ← smt.bitblast.mk_add XY Z,
--   X_YZ ← smt.bitblast.mk_add X YZ,
--   eq ← smt.bitblast.mk_eq XY_Z X_YZ,
--   sat.not_factory.mk_not eq

-- lemma mem_mk_add_assoc_circuit (x y z : fin n → bool) (g : γ) :
--   ((mk_add_assoc_circuit n β γ x y z).run g).1 ∈ ((mk_add_assoc_circuit n β γ x y z).run g).2 :=
-- begin
--   simp only [mk_add_assoc_circuit, state_t.run_bind],
--   simp only [has_bind.bind, id_bind],
--   solve_by_elim only [
--     sat.factory.mem_of_le,
--     smt.bitblast.le_mk_var,
--     smt.bitblast.mem_mk_var,
--     smt.bitblast.le_mk_add,
--     smt.bitblast.mem_mk_add,
--     smt.bitblast.le_mk_eq,
--     smt.bitblast.mem_mk_eq,
--     sat.not_factory.le_mk_not,
--     sat.not_factory.mem_mk_not
--   ] { max_depth := 80, pre_apply := tactic.intros >> pure () },
-- end

-- lemma unsat_mk_add_assoc_circuit (x y z : fin n → bool) (g : γ) :
--   !((mk_add_assoc_circuit n β γ x y z).run g).1 → ((x + y) + z) = (x + (y + z)) :=
-- begin
--   simp only [mk_add_assoc_circuit, state_t.run_bind],
--   simp only [has_bind.bind, id_bind],
--   simp only [
--     sat.not_factory.sat_mk_not,
--     smt.bitblast.sat_mk_add,
--     smt.bitblast.sat_mk_var,
--     smt.bitblast.sat_mk_eq,
--     bnot_bnot,
--     bv.all_iff,
--     biff_coe_iff,
--     vector.nth_of_fn ],
--   intros unsat,
--   funext,
--   specialize unsat i,
--   rw [bool.coe_bool_iff] at unsat,
--   from unsat,
-- end

-- end

-- def add_assoc_aig (n : ℕ) (x y z : fin n → bool) : (aig.ref pos_num × aig.factory pos_num) :=
--   ((mk_add_assoc_circuit n (aig.ref pos_num) _ x y z).run aig.factory.init)

-- -- #eval aig.ref.to_cnf (trie unit) $ (add_assoc_aig 8 (default _) (default _) (default _)).1

-- theorem add8_associative (x y z : fin 8 → bool) :
--   ((x + y) + z) = (x + (y + z)) :=
-- begin
--   -- apply unsat_mk_add_assoc_circuit _ (aig.ref pos_num) (aig.factory pos_num) x y z aig.factory.init,
--   -- apply @aig.bnot_of_unsat_to_cnf _ _ _ (trie unit) _ _ _ _ (mem_mk_add_assoc_circuit _ _ _ _ _ _ _),
--   sorry,
-- end

-- end add_associativity
