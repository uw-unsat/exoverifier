/-
Copyright (c) 2021 The UNSAT Group. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luke Nelson, Xi Wang
-/
import aig.aiger
import aig.to_cnf
import bpf.absint.basic
import bpf.basic
import bpf.simplechecker.basic
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

meta def program_expr :=
``(%%program_meta)

def program : bpf.cfg.trie_program :=
(by tactic.to_expr program_expr >>= tactic.exact)

def program_safety : bpf.cfg.safe program :=
bpf.simplechecker.check_sound 150 (by refl)

end test_bpf
