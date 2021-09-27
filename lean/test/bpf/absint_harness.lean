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

meta def progbits : list bool :=
(by tactic.io.from_le_quadword_file_as_be_bits
  (by tactic.io.from_env_var "BPF_BIN_PATH" "test/bpf/examples/absint/simple1.bin"))

meta def o_program : option bpf.cfg.trie_program :=
bpf.decode progbits >>= λ x, pure $ bpf.cfg.trie_program.decode_from_flat x

meta def program_meta : bpf.cfg.trie_program :=
option.iget o_program

meta def program_expr : pexpr :=
to_pexpr program_meta

def program : bpf.cfg.trie_program :=
(by tactic.to_expr program_expr >>= tactic.exact)

def constraints := @ai.gen_constraints pos_num (bpf.reg → tnum 64) _ _ trie _ program

meta def solution : ai.STATE :=
 @ai.solve pos_num (bpf.reg → tnum 64) _ _ trie _ constraints 2

meta def solexpr : pexpr :=
``(%%solution : @ai.STATE (bpf.reg → tnum 64) _ trie)

/-- The solution, but reified into a concrete trie (no computation),
    by doing computation in meta-lean and serializing. -/
def solution' : @ai.STATE (bpf.reg → tnum 64) _ trie :=
(by tactic.to_expr solexpr >>= tactic.exact)

def predicates := @ai.gen_safety pos_num (bpf.reg → tnum 64) _ _ trie _ program

def program_safety : bpf.cfg.safe program :=
ai.safe_program_of_correct_approximation _ solution' dec_trivial dec_trivial

end test_bpf
