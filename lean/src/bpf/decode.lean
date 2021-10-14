/-
Copyright (c) 2021 The UNSAT Group. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luke Nelson, Xi Wang
-/
import .basic

namespace bpf
open reg

private def decode_reg : list bool → option reg
| [ff, ff, ff, ff] := R0
| [ff, ff, ff, tt] := R1
| [ff, ff, tt, ff] := R2
| [ff, ff, tt, tt] := R3
| [ff, tt, ff, ff] := R4
| [ff, tt, ff, tt] := R5
| [ff, tt, tt, ff] := R6
| [ff, tt, tt, tt] := R7
| [tt, ff, ff, ff] := R8
| [tt, ff, ff, tt] := R9
| [tt, ff, tt, ff] := FP
| [tt, ff, tt, tt] := AX
| _ := none

private def decode_alu_op : list bool → option ALU
| [ff, ff, ff, ff] := some ALU.ADD
| [ff, ff, ff, tt] := some ALU.SUB
| [ff, ff, tt, ff] := some ALU.MUL
| [ff, ff, tt, tt] := some ALU.DIV
| [ff, tt, ff, ff] := some ALU.OR
| [ff, tt, ff, tt] := some ALU.AND
| [ff, tt, tt, ff] := some ALU.LSH
| [ff, tt, tt, tt] := some ALU.RSH
| [tt, ff, ff, ff] := some ALU.NEG
| [tt, ff, ff, tt] := some ALU.MOD
| [tt, ff, tt, ff] := some ALU.XOR
| [tt, ff, tt, tt] := some ALU.MOV
| [tt, tt, ff, ff] := some ALU.ARSH
| [tt, tt, ff, tt] := some ALU.END
| _ := none

private def decode_jmp_op : list bool → option JMP
| [ff, ff, ff, tt] := some JMP.JEQ  /- 0x1 -/
| [ff, ff, tt, ff] := some JMP.JGT  /- 0x2 -/
| [ff, ff, tt, tt] := some JMP.JGE  /- 0x3 -/
| [ff, tt, ff, ff] := some JMP.JSET /- 0x4 -/
| [ff, tt, ff, tt] := some JMP.JNE  /- 0x5 -/
| [ff, tt, tt, ff] := some JMP.JSGT /- 0x6 -/
| [ff, tt, tt, tt] := some JMP.JSGE /- 0x7 -/
/- [tt, ff, ff, ff] Skip 0x8: BPF_CALL -/
/- [tt, ff, ff, tt] Skip 0x9: BPF_EXIT -/
| [tt, ff, tt, ff] := some JMP.JLT  /- 0xa -/
| [tt, ff, tt, tt] := some JMP.JLE  /- 0xb -/
| [tt, tt, ff, ff] := some JMP.JSLT /- 0xc -/
| [tt, tt, ff, tt] := some JMP.JSLE /- 0xd -/
| _                := none

private def decode_jmp_x : reg → reg → msbvector 16 → list bool → option instr
| dst src off op := do
  op' ← decode_jmp_op op,
  pure $ instr.JMP_X op' dst src off

private def decode_call : list bool → option instr
| [ff, ff, ff, ff, ff, ff, ff, ff,
   ff, ff, ff, ff, ff, ff, ff, ff,
   ff, ff, ff, ff, ff, ff, ff, ff,
   ff, ff, ff, ff, ff, tt, tt, tt] := some $ instr.CALL BPF_FUNC.get_prandom_u32
| _ := none

private def decode_jmp_k : reg → msbvector 32 → msbvector 16 → list bool → option instr
| dst imm off [tt, ff, ff, ff] := decode_call imm.to_list
| dst imm off [tt, ff, ff, tt] := some $ instr.Exit
| dst imm off op := do
  op' ← decode_jmp_op op,
  pure $ instr.JMP_K op' dst imm off

private def decode_mem_size : list bool → option SIZE
| [ff, ff] := some SIZE.W  /- 0x00 >> 3 -/
| [ff, tt] := some SIZE.H  /- 0x08 >> 3 -/
| [tt, ff] := some SIZE.B  /- 0x10 >> 3 -/
| [tt, tt] := some SIZE.DW /- 0x18 >> 3 -/
| _        := none

private def decode_op : msbvector 32 → msbvector 16 → reg → reg → list bool → option instr
/- BPF_ALU64 | BPF_X -/
| imm off dst src [op₁, op₂, op₃, op₄, tt, tt, tt, tt] := do
  op ← decode_alu_op [op₁, op₂, op₃, op₄],
  some $ instr.ALU64_X op dst src

/- BPF_ALU64 | BPF_K -/
| imm off dst src [op₁, op₂, op₃, op₄, ff, tt, tt, tt] := do
  op ← decode_alu_op [op₁, op₂, op₃, op₄],
  some $ instr.ALU64_K op dst imm

/- BPF_MEM | BPF_STX -/
| imm off dst src [ff, tt, tt, size₁, size₂, ff, tt, tt] := do
  size ← decode_mem_size [size₁, size₂],
  some $ instr.STX size dst src off

/- BPF_JMP | BPF_X -/
| imm off dst src [op₁, op₂, op₃, op₄, tt, tt, ff, tt] :=
  decode_jmp_x dst src off [op₁, op₂, op₃, op₄]

/- BPF_JMP | BPF_K -/
| imm off dst src [op₁, op₂, op₃, op₄, ff, tt, ff, tt] :=
  decode_jmp_k dst imm off [op₁, op₂, op₃, op₄]

| _ _ _ _ _ := none

private def decode_core : list bool → list instr → option (list instr)
| (imm₁  :: imm₂  :: imm₃  :: imm₄  :: imm₅  :: imm₆  :: imm₇  :: imm₈  :: imm₉  :: imm₁₀ :: imm₁₁ :: imm₁₂ :: imm₁₃ :: imm₁₄ :: imm₁₅ :: imm₁₆ ::
   imm₁₇ :: imm₁₈ :: imm₁₉ :: imm₂₀ :: imm₂₁ :: imm₂₂ :: imm₂₃ :: imm₂₄ :: imm₂₅ :: imm₂₆ :: imm₂₇ :: imm₂₈ :: imm₂₉ :: imm₃₀ :: imm₃₁ :: imm₃₂ ::
   off₁ :: off₂ :: off₃ :: off₄ :: off₅ :: off₆ :: off₇ :: off₈ :: off₉ :: off₁₀ :: off₁₁ :: off₁₂ :: off₁₃ :: off₁₄ :: off₁₅ :: off₁₆ ::
   src₁ :: src₂ :: src₃ :: src₄ :: dst₁ :: dst₂ :: dst₃ :: dst₄ :: op₁ :: op₂ :: op₃ :: op₄ :: op₅ :: op₆ :: op₇ :: op₈ :: tl) is :=
  let imm32 : vector bool 32 :=
    imm₁  ::ᵥ imm₂  ::ᵥ imm₃  ::ᵥ imm₄  ::ᵥ imm₅  ::ᵥ imm₆  ::ᵥ imm₇  ::ᵥ imm₈  ::ᵥ imm₉  ::ᵥ imm₁₀ ::ᵥ imm₁₁ ::ᵥ imm₁₂ ::ᵥ imm₁₃ ::ᵥ imm₁₄ ::ᵥ imm₁₅ ::ᵥ imm₁₆ ::ᵥ
    imm₁₇ ::ᵥ imm₁₈ ::ᵥ imm₁₉ ::ᵥ imm₂₀ ::ᵥ imm₂₁ ::ᵥ imm₂₂ ::ᵥ imm₂₃ ::ᵥ imm₂₄ ::ᵥ imm₂₅ ::ᵥ imm₂₆ ::ᵥ imm₂₇ ::ᵥ imm₂₈ ::ᵥ imm₂₉ ::ᵥ imm₃₀ ::ᵥ imm₃₁ ::ᵥ imm₃₂ ::ᵥ vector.nil in
  let off16 : vector bool 16 :=
    off₁ ::ᵥ off₂ ::ᵥ off₃ ::ᵥ off₄ ::ᵥ off₅ ::ᵥ off₆ ::ᵥ off₇ ::ᵥ off₈ ::ᵥ off₉ ::ᵥ off₁₀ ::ᵥ off₁₁ ::ᵥ off₁₂ ::ᵥ off₁₃ ::ᵥ off₁₄ ::ᵥ off₁₅ ::ᵥ off₁₆ ::ᵥ vector.nil in do
  dst ← decode_reg [dst₁, dst₂, dst₃, dst₄],
  src ← decode_reg [src₁, src₂, src₃, src₄],
  i ← decode_op imm32 off16 dst src [op₁, op₂, op₃, op₄, op₅, op₆, op₇, op₈],
  decode_core tl (i :: is)
| [] is := pure is
| _  _  := none

/-- Decode a list of bits as a list of BPF instructions. -/
def decode (l : list bool) : option (list instr) :=
  (decode_core l []).map(λ l, l.reverse)

end bpf
