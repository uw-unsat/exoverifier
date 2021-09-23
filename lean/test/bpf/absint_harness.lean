/-
Copyright (c) 2021 The UNSAT Group. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luke Nelson, Xi Wang
-/
import aig.aiger
import aig.to_cnf
import bpf.absint.basic
import bpf.basic
import bpf.decode
import data.domain.tnum
import sat.tactic
import tactic.io

namespace test_bpf

def progbits : list bool :=
(by tactic.io.from_le_quadword_file_as_be_bits
  (by tactic.io.from_env_var "BPF_BIN_PATH" "test/bpf/examples/absint/simple1.bin"))

def program' : option bpf.cfg.trie_program :=
bpf.decode progbits >>= λ x, pure $ bpf.cfg.trie_program.decode_from_flat x

def program : bpf.cfg.trie_program :=
option.iget program'

-- #eval program

def constraints := @ai.gen_constraints pos_num (bpf.reg → tnum 64) _ _ trie _ program

def solution : ai.STATE :=
 @ai.solve pos_num (bpf.reg → tnum 64) _ _ trie _ constraints 2

meta def solexpr :=
  let s := has_serialize.serialize solution in reflected_value.mk s

/-- The solution, but reified into a concrete trie (no computation),
    by doing computation in meta-lean and serializing. -/
def solution' : @ai.STATE (bpf.reg → tnum 64) _ trie :=
has_serialize.deserialize (by tactic.exact solexpr.expr)

-- meta def foo := `(solution)

-- #check foo

-- #check (has_reify.deserialize (has_reify.serialize solution)) : ai.STATE

def predicates := @ai.gen_safety pos_num (bpf.reg → tnum 64) _ _ trie _ program

-- #eval solution

-- #eval to_bool (ai.approximates program solution)
-- #eval to_bool (ai.secure program solution)

def program_safety : bpf.cfg.safe program :=
ai.safe_program_of_correct_approximation _ solution' dec_trivial dec_trivial

-- #eval constraints
-- def test_absint_soundness (p : bpf.cfg.trie_program) :=
-- @bpf.cfg.absint.safe_of_run_exited pos_num (with_top $ id bpf.i64) _ _ _ _ p 2048

-- @[reducible]
-- def spec (p : list bool) : Prop :=
-- ∃ (cfg : bpf.cfg.trie_program),
--   (bpf.decode p).map bpf.cfg.trie_program.decode_from_flat = some cfg ∧
--   bpf.cfg.safe cfg

-- def prog_ok : spec progbits :=
-- ⟨_, and.intro rfl (test_absint_soundness _ _ (by refl))⟩

end test_bpf
