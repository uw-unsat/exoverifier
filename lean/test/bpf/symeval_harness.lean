/-
Copyright (c) 2021 The UNSAT Group. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luke Nelson, Xi Wang
-/
import aig.aiger
import aig.to_cnf
import bpf.basic
import bpf.decision
import bpf.decode
import bpf.se.basic
import bpf.se.default
import bpf.se.soundness
import bpf.spec
import factory.interface
import sat.default
import sat.factory
import sat.tactic
import smt.bitblast
import tactic.debug
import tactic.io

def fuel : ℕ := 24

namespace test_bpf

@[reducible]
def zregs : vector bpf.i64 bpf.nregs := vector.repeat (λ _, ff) _

meta def bpf_path : string := (by tactic.io.from_env_var "BPF_BIN_PATH" "test/bpf/examples/symeval/nonzero-division.bin")

def progbits : list bool :=
(by tactic.io.from_le_quadword_file_as_be_bits bpf_path)

def proof : sat.proof.default.proof :=
by semidecision.by_oracle (bpf.decision.default.binary_safety_via_reduce_to_smt_oracle fuel) (default _, progbits)

theorem binary_program_safety : bpf.binary_safe progbits :=
bpf.safe_of_erased_regs $
λ regs, semidec_trivial (bpf.decision.default.decide_binary_safety_via_reduce_to_smt fuel (regs, progbits) proof)

def program : bpf.cfg.trie_program :=
(by tactic.io.exact_io $ tactic.io.read_le_quadword_file_as_bpf_program bpf_path)

theorem program_safety : bpf.cfg.safe program :=
bpf.trie_safe_of_erased_regs $
λ regs, semidec_trivial (bpf.decision.default.decide_safe_with_regs_via_reduce_to_smt fuel (program, regs) proof)

end test_bpf
