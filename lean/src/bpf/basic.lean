/-
Copyright (c) 2021 The UNSAT Group. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luke Nelson, Xi Wang
-/
import data.bitvec.basic
import data.bv.basic
import data.bv.vector
import data.list.alist
import data.trie.basic
import data.vector
import misc.vector
import misc.reify
import tactic.basic
import tactic.derive_fintype

namespace bpf

abbreviation i64 : Type := fin 64 → bool
abbreviation i32 : Type := fin 32 → bool

/-- Truncate a 64-bit value to the lower 32 bits. -/
@[reducible]
private def trunc32 (i : i64) : i32 :=
bv.extract 31 0 (dec_trivial : 31 < 64) dec_trivial i

/-- The number of BPF registers. -/
abbreviation nregs : ℕ := 12

@[derive [decidable_eq, inhabited, has_reflect, fintype]]
inductive reg : Type
| R0
| R1
| R2
| R3
| R4
| R5
| R6
| R7
| R8
| R9
| FP
| AX

namespace reg

def to_vector {α : Type*} (regs : reg → α) : vector α nregs :=
regs R0 ::ᵥ regs R1 ::ᵥ regs R2 ::ᵥ regs R3 ::ᵥ regs R4 ::ᵥ
regs R5 ::ᵥ regs R6 ::ᵥ regs R7 ::ᵥ regs R8 ::ᵥ regs R9 ::ᵥ
regs FP ::ᵥ regs AX ::ᵥ vector.nil

def to_fin : reg → fin nregs
| R0 := 0
| R1 := 1
| R2 := 2
| R3 := 3
| R4 := 4
| R5 := 5
| R6 := 6
| R7 := 7
| R8 := 8
| R9 := 9
| FP := 10
| AX := 11

def of_vector {α : Type*} (v : vector α nregs) (r : reg) : α :=
v.nth r.to_fin

theorem to_of_vector {α : Type*} (regs : reg → α) :
  of_vector (to_vector regs) = regs :=
by { ext i, cases i; refl }

theorem of_to_vector {α : Type*} (v : vector α nregs) :
  to_vector (of_vector v) = v :=
begin
  ext i,
  repeat {
    refine fin.cases _ _ i,
    refl,
    intros i },
  exact fin.elim0 i
end

instance : has_repr reg :=
⟨λ r,
  match r with
  | R0 := "R0"
  | R1 := "R1"
  | R2 := "R2"
  | R3 := "R3"
  | R4 := "R4"
  | R5 := "R5"
  | R6 := "R6"
  | R7 := "R7"
  | R8 := "R8"
  | R9 := "R9"
  | FP := "FP"
  | AX := "AX"
  end⟩

end reg

/-- Size operands for memory instructions. -/
@[derive [decidable_eq, inhabited, has_reflect, fintype]]
inductive SIZE : Type
| B
| H
| W
| DW

namespace SIZE

def repr : SIZE → string
| B  := "B"
| H  := "H"
| W  := "W"
| DW := "DW"

instance : has_repr SIZE := ⟨repr⟩

end SIZE

/-- Arithmetic opcodes. -/
@[derive [decidable_eq, inhabited, has_reflect, fintype]]
inductive ALU : Type
| ADD
| SUB
| MUL
| DIV
| OR
| AND
| LSH
| RSH
| NEG
| MOD
| XOR
| MOV
| ARSH
| END

namespace ALU

def repr : ALU → string
| ADD  := "ADD"
| SUB  := "SUB"
| MUL  := "MUL"
| DIV  := "DIV"
| OR   := "OR"
| AND  := "AND"
| LSH  := "LSH"
| RSH  := "RSH"
| NEG  := "NEG"
| MOD  := "MOD"
| XOR  := "XOR"
| MOV  := "MOV"
| ARSH := "ARSH"
| END  := "END"

instance : has_repr ALU := ⟨repr⟩

/-- Whether a particular ALU operation is allowed. -/
def ALU_check {n : ℕ} : ALU → (fin n → bool) → (fin n → bool) → bool
| DIV x y  := y ≠ 0 -- Disallow division by zero.
| MOD x y  := ff -- Disallow mod for now TODO
| END x y  := ff -- Disallow endianness conversion for now TODO
| _ x y    := tt

abbreviation ALU64_check : ALU → i64 → i64 → bool := ALU_check

/-- The result of an ALU operation. -/
def doALU {n : ℕ} : ALU → (fin n → bool) → (fin n → bool) → (fin n → bool)
| ADD x y  := x + y
| SUB x y  := x - y
| MUL x y  := x * y
| DIV x y  := x / y
| OR x y   := bv.or x y
| AND x y  := bv.and x y
| LSH x y  := bv.shl x y
| RSH x y  := bv.lshr x y
| NEG x _  := -x
| MOD x y  := x % y
| XOR x y  := bv.xor x y
| MOV _ y  := y
| ARSH x y := bv.ashr x y
| END x y  := 0 -- TODO

/-- 64-bit ALU operation abbreviation. -/
abbreviation doALU64 : ALU → i64 → i64 → i64 := doALU

/--
Perform a 32-bit ALU operation by truncating registers to 32 bits and zero-extending
the result back to 64 bits.
-/
@[reducible]
def doALU32 (op : ALU) (x y : i64) : i64 :=
bv.concat (0 : i32) (doALU op (trunc32 x) (trunc32 y))

end ALU

@[derive [decidable_eq, inhabited, has_reflect, fintype]]
inductive JMP : Type
| JEQ
| JNE
| JLE
| JLT
| JGE
| JGT
| JSLE
| JSLT
| JSGE
| JSGT
| JSET

namespace JMP

def repr : JMP → string
| JEQ  := "JEQ"
| JNE  := "JNE"
| JLE  := "JLE"
| JLT  := "JLT"
| JGE  := "JGE"
| JGT  := "JGT"
| JSLE := "JSLE"
| JSLT := "JSLT"
| JSGE := "JSGE"
| JSGT := "JSGT"
| JSET := "JSET"

instance : has_repr JMP := ⟨repr⟩

/-- Evaluate a JMP condition on two concrete bitvectors. -/
def doJMP {n : ℕ} : JMP → (fin n → bool) → (fin n → bool) → bool
| JEQ x y  := x = y
| JNE x y  := x ≠ y
| JLE x y  := x ≤ y
| JLT x y  := x < y
| JGE x y  := x ≥ y
| JGT x y  := x > y
| JSLE x y := bv.sle x y
| JSLT x y := bv.slt x y
| JSGE x y := bv.sge x y
| JSGT x y := bv.sgt x y
| JSET x y := bv.and x y ≠ 0

/-- 64-bit JMP operation abbreviation. -/
abbreviation doJMP64 : JMP → i64 → i64 → bool := @doJMP 64

/-- Evaluate a 32-bit JMP operation on 64-bit operands taking the lower 32 bits of inputs. -/
@[reducible]
def doJMP32 (op : JMP) (x y : i64) : bool :=
@doJMP 32 op (trunc32 x) (trunc32 y)

end JMP

/--
Low-level representation of BPF instructions. In this format, jump offsets are still encoded
as bitvector offsets in the instruction stream. See `cfg.lean` for the higher-level representation
used for analysis.

Note: Unlike most of our bitvector infrastructure, bitvectors in this format have the _MSB_ at
bit index 0, which matches the built-in library Lean has for operations on `vector bool n`, and
simplifies the job of the decoder. When we parse this to the CFG format, we must be careful flip
bit ordering accordingly.
-/
@[derive [has_reflect, decidable_eq]]
inductive instr : Type
| ALU64_X : ALU → reg → reg → instr
| ALU64_K : ALU → reg → msbvector 32 → instr
| JMP_X   : JMP → reg → reg → msbvector 16 → instr
| JMP_K   : JMP → reg → msbvector 32 → msbvector 16 → instr
| Exit    : instr

namespace instr

private def repr' : instr → string
| (ALU64_X op dst src)   := "ALU64_X " ++ repr op ++ " " ++ repr dst ++ " " ++ repr src
| (ALU64_K op dst imm)   := "ALU64_K " ++ repr op ++ " " ++ repr dst ++ " " ++ repr imm
| (JMP_X op dst src off) := "JMP_X " ++ repr op ++ " " ++ repr dst ++ " " ++ repr src ++ " " ++ repr off
| (JMP_K op dst imm off) := "JMP_K " ++ repr op ++ " " ++ repr dst ++ " " ++ repr imm ++ " " ++ repr off
| Exit                   := "Exit"

instance : has_repr instr := ⟨repr'⟩

end instr
end bpf
