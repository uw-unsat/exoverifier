/-
Copyright (c) 2021 The UNSAT Group. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luke Nelson, Xi Wang
-/
-- import aig.to_cnf
-- import smt.basic
-- import smt.factory
-- import data.bv.basic
-- import sat.tactic

-- lemma nth_of_fn_ext {α : Type*} {n : ℕ} (f : fin n → α) :
--   (vector.of_fn f).nth = f := by funext; simp [vector.of_fn_nth]

-- section add_commutativity

-- section
-- universe u
-- variables (n : ℕ) (α β γ : Type u)
-- variables [counter α]
-- variables [sat.factory β γ] [sat.iff_factory β γ] [sat.or_factory β γ] [sat.var_factory β γ] [sat.xor_factory β γ] [sat.all_factory β γ] [sat.and_factory β γ] [sat.any_factory β γ] [sat.const_factory β γ]

-- def mk_add_comm_expr (x y : fin n → bool) : state (smt.factory α β γ) (smt.formula α β 1) := do
-- X ← smt.factory.mk_var (vector.of_fn x),
-- Y ← smt.factory.mk_var (vector.of_fn y),
-- XY ← smt.factory.mk_add X Y,
-- YX ← smt.factory.mk_add Y X,
-- smt.factory.mk_eq XY YX

-- lemma mem_mk_add_comm_expr (x y : fin n → bool) (g : smt.factory α β γ) :
--   ((mk_add_comm_expr n α β γ x y).run g).2.owns ((mk_add_comm_expr n α β γ x y).run g).1 :=
-- begin
--   simp only [mk_add_comm_expr, state_t.run_bind],
--   simp only [has_bind.bind, id_bind],
--   apply smt.factory.mem_mk_eq,
--   { apply smt.factory.owns_of_le,
--     apply smt.factory.le_mk_add,
--     apply smt.factory.mem_mk_add,
--     apply smt.factory.owns_of_le,
--     apply smt.factory.le_mk_var,
--     apply smt.factory.mem_mk_var,
--     apply smt.factory.mem_mk_var },
--   { apply smt.factory.mem_mk_add,
--     apply smt.factory.owns_of_le,
--     apply smt.factory.le_mk_add,
--     apply smt.factory.mem_mk_var,
--     apply smt.factory.owns_of_le,
--     apply smt.factory.le_mk_add,
--     apply smt.factory.owns_of_le,
--     apply smt.factory.le_mk_var,
--     apply smt.factory.mem_mk_var }
-- end

-- lemma add_comm_expr_true_iff (x y : fin n → bool) (g : smt.factory α β γ):
--   (((mk_add_comm_expr n α β γ x y).run g).1 : fin 1 → bool) 0 ↔ (x + y = y + x) :=
-- begin
--   simp only [mk_add_comm_expr, smt.formula.coe_fin_eq_eval, state_t.run_bind],
--   simp only [has_bind.bind, id_bind],
--   simp only [smt.factory.mk_eq, smt.factory.mk_var, smt.factory.mk_add, smt.formula.eval, nth_of_fn_ext, bool.of_to_bool_iff],
-- end

-- end

-- lemma add32_comm (x y : fin 32 → bool) :
--   x + y = y + x :=
-- begin
--   -- First rewrite is based on the evaluation of the SMT expression.
--   rw ← add_comm_expr_true_iff _ pos_num (aig.ref pos_num) (aig.factory pos_num) _ _ (smt.factory.init aig.factory.init),
--   -- Obtain proof of membership of the expression in the factory
--   obtain owns := smt.factory.owns_root_of_owns (mem_mk_add_comm_expr 32 pos_num (aig.ref pos_num) (aig.factory pos_num) x y _),
--   -- Rewrite according to wf (soundness of circuits embedded in expressions)
--   rw owns.wf,
--   -- Soundness of conversion from aig to cnf.
--   -- apply @aig.true_of_unsat_of_not_to_cnf _ _ _ (trie unit) _ _ _ _ _ _, swap,
--   -- Prove that the circuit is in the factory.
--   -- { apply owns.circuit_mem },
--   -- Show unsatisfiability of CNF. TODO
--   sorry,
-- end

-- end add_commutativity

-- -- theorem add32_commutative (x y z : fin 32 → bool) :
-- --   (x + y) = (y + x) :=
-- -- begin
-- -- end
