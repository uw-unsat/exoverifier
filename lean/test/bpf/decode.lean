/-
Copyright (c) 2021 The UNSAT Group. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luke Nelson, Xi Wang
-/
import bpf.basic
import bpf.decode
import data.bitvec.basic
import data.buffer
import tactic.io

open bpf

meta def file (s : string) : tactic unit :=
`[tactic.io.from_le_quadword_file_as_be_bits $ "test/bpf/examples/" ++ s]

example : bpf.decode (by file "common/test-decode.bin") = some [
  instr.ALU64_K ALU.MOV bpf.reg.R1 (vector.of_fn (λ x, if x = 31 then tt else ff)),
  instr.ALU64_X ALU.ADD bpf.reg.R1 bpf.reg.R2,
  instr.ALU64_X ALU.SUB bpf.reg.R1 bpf.reg.R2,
  instr.ALU64_X ALU.MUL bpf.reg.R1 bpf.reg.R2,
  instr.ALU64_X ALU.DIV bpf.reg.R1 bpf.reg.R2,
  instr.ALU64_X ALU.OR bpf.reg.R1 bpf.reg.R2,
  instr.ALU64_X ALU.AND bpf.reg.R1 bpf.reg.R2,
  instr.ALU64_X ALU.LSH bpf.reg.R1 bpf.reg.R2,
  instr.ALU64_X ALU.RSH bpf.reg.R1 bpf.reg.R2,
  instr.ALU64_K ALU.NEG bpf.reg.R1 0,
  instr.ALU64_X ALU.XOR bpf.reg.R1 bpf.reg.R2,
  instr.ALU64_X ALU.MOV bpf.reg.R1 bpf.reg.R2,
  instr.ALU64_X ALU.ARSH bpf.reg.R1 bpf.reg.R2,
  instr.Exit
] := by {
  refl,
}
