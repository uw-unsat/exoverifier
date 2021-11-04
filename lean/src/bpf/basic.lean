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
import misc.fin_enum
import tactic.basic
import data.equiv.basic
import tactic.derive_fintype

namespace bpf

abbreviation i64 : Type := fin 64 → bool
abbreviation i32 : Type := fin 32 → bool

/- An oracle makes the nondeterministic choices during execution of a BPF program. -/
structure oracle : Type :=
(rng          : ℕ → i64)

namespace oracle

instance : inhabited oracle :=
⟨⟨ λ _, default _ ⟩⟩

end oracle

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

/-- Caller-saved registers according to the BPF semantics. -/
def caller_saved : list reg :=
[R0, R1, R2, R3, R4, R5]

def to_vector {α : Type*} (regs : reg → α) : vector α nregs :=
regs R0 ::ᵥ regs R1 ::ᵥ regs R2 ::ᵥ regs R3 ::ᵥ regs R4 ::ᵥ
regs R5 ::ᵥ regs R6 ::ᵥ regs R7 ::ᵥ regs R8 ::ᵥ regs R9 ::ᵥ
regs FP ::ᵥ regs AX ::ᵥ vector.nil

/-- `reg` is finite and enumerable. -/
instance : fin_enum reg :=
fin_enum.of_list [R0, R1, R2, R3, R4, R5, R6, R7, R8, R9, FP, AX]
                 (by intros x; cases x; simp)

def to_fin : reg → fin nregs :=
λ k, (fin_enum.equiv reg).to_fun k

theorem to_fin_inj {r₁ r₂ : reg} :
  (to_fin r₁) = (to_fin r₂) →
  r₁ = r₂ :=
begin
  simp only [to_fin],
  intros h₂,
  apply equiv.injective (fin_enum.equiv reg) h₂
end

@[simp]
theorem to_fin_eq_eq_eq {r₁ r₂ : reg} :
  (to_fin r₁) = (to_fin r₂) ↔ r₁ = r₂ :=
begin
  split; intros; try{tauto},
  apply to_fin_inj; assumption
end

theorem to_fin_ne_of_ne {r₁ r₂ : reg} :
  r₁ ≠ r₂ →
  (to_fin r₁) ≠ (to_fin r₂) :=
begin
  intros h,
  contrapose! h,
  exact to_fin_inj h
end

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

private def repr : SIZE → string
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

/- Opaque memory region. -/
@[derive [decidable_eq, has_reflect, inhabited]]
structure memregion : Type

/- A value is either a 64-bit scalar, a memory region + offset, or uninitialized. -/
@[derive [decidable_eq]]
inductive value : Type
| scalar        : i64 → value
| pointer       : memregion → i64 → value
| uninitialized : value

namespace value

instance : inhabited value := ⟨value.scalar 0⟩

abbreviation is_scalar (v : value) : Prop :=
∃ r, v = scalar r

instance : decidable_pred is_scalar
| (scalar x)    := decidable.is_true ⟨x, rfl⟩
| (pointer _ _) := decidable.is_false (by { intros h, cases h with _ h, cases h })
| uninitialized := decidable.is_false (by { intros h, cases h with _ h, cases h })

abbreviation is_uninitialized (v : value) : Prop :=
v = uninitialized

end value

namespace ALU

private def repr : ALU → string
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

/-- Whether a particular ALU64 operation is allowed. -/
def doALU64_scalar_check : ALU → i64 → i64 → bool
| DIV x y  := y ≠ 0 -- Disallow division by zero.
| MOD x y  := y ≠ 0 -- Disallow mod by zero.
| LSH x y  := y < 64 -- Prohibit oversized shift.
| RSH x y  := y < 64 -- Prohibit oversized shift.
| ARSH x y := y < 64 -- Prohibit oversized shift.
| END x y  := ff -- Disallow endianness conversion for now TODO
| _ x y    := tt

/-- Whether a particular ALU32 operation is allowed. -/
def doALU32_scalar_check : ALU → i32 → i32 → bool
| DIV x y  := y ≠ 0 -- Disallow division by zero.
| MOD x y  := y ≠ 0 -- Disallow mod by zero.
| LSH x y  := y < 32 -- Prohibit oversized shift.
| RSH x y  := y < 32 -- Prohibit oversized shift.
| ARSH x y := y < 32 -- Prohibit oversized shift.
| END x y  := ff -- Disallow endianness conversion for now TODO
| _ x y    := tt

def doALU_pointer_scalar_check : ALU → bool
| ADD := tt
| SUB := tt
| MOV := tt
| _   := ff

/-
Lean is not good at simplifying multi-way matches like `doALU_check` here.
To make proofs easier to write without case explosion, we write simplification
lemmas for each branch of the match. We make a custom simp attribute for
these simplification lemmas to avoid polluting the global simp set or
paying for the performance / fragility of bare `simp` in proofs.

One can use a tactic like the following to use these match simplification lemmas
(in addition to some other lemmas X, Y, and Z, for example).
`simp only [X, Y, Z] with match_simp`
-/
mk_simp_attribute match_simp "Simplification lemmas for multi-way matches."

@[match_simp]
def doALU64_check : ALU → value → value → bool
| op (value.scalar x) (value.scalar y) := doALU64_scalar_check op x y

| op (value.pointer _ _) (value.scalar _) := doALU_pointer_scalar_check op

/- It is legal to move pointers and scalars into uninitialized registers. -/
| op _ (value.scalar _)    := if op = ALU.MOV then tt else ff
| op _ (value.pointer _ _) := if op = ALU.MOV then tt else ff

/- Remaining ops are illegal. -/
| _ _ _       := ff

@[match_simp]
private theorem doALU_check_pointer_def (op : ALU) {x m y} :
  op.doALU64_check x (value.pointer m y) = if op = ALU.MOV then tt else ff :=
by cases x; refl

@[match_simp]
private theorem doALU_check_pointer_scalar (op : ALU) {x m y} :
  op.doALU64_check (value.pointer m x) (value.scalar y) = op.doALU_pointer_scalar_check :=
by refl

@[match_simp]
private theorem doALU_check_scalar_def (op : ALU) (x y : i64) :
  op.doALU64_check (value.scalar x) (value.scalar y) = doALU64_scalar_check op x y :=
by refl

@[match_simp]
private theorem doALU_check_mov_scalar_def {x} (y : i64) :
  MOV.doALU64_check x (value.scalar y) = tt :=
by cases x; refl

@[match_simp]
private theorem doALU_check_mov_pointer_def {x m} (y : i64) :
  MOV.doALU64_check x (value.pointer m y) = tt :=
by cases x; refl

@[match_simp]
private theorem doALU_check_uninitialized_def (op : ALU) (a) :
  op.doALU64_check a value.uninitialized = ff:=
by cases op; cases a; refl

@[match_simp]
def doALU32_check : ALU → value → value → bool
| op (value.scalar x) (value.scalar y) := doALU32_scalar_check op (trunc32 x) (trunc32 y)

/- It is legal to move scalars into uninitialized registers. -/
| op _ (value.scalar _) := if op = ALU.MOV then tt else ff

/- Remaining ops are illegal. -/
| _ _ _       := ff

/-- The result of an ALU operation. -/
private def doALU_scalar {n : ℕ} : ALU → (fin n → bool) → (fin n → bool) → (fin n → bool)
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
| END x y  := x -- TODO

def doALU64_scalar := @doALU_scalar 64

@[match_simp]
def doALU_pointer_scalar : ALU → memregion → i64 → i64 → value
| ADD m off val := value.pointer m (off + val)
| SUB m off val := value.pointer m (off - val)
| MOV _ _   val := value.scalar val
| _   m off _   := value.pointer m off

@[match_simp]
def doALU64 : ALU → value → value → value
| op (value.scalar x) (value.scalar y) := value.scalar (op.doALU64_scalar x y)
| op (value.pointer m off) (value.scalar val) := op.doALU_pointer_scalar m off val

/- MOV always returns src. -/
| ALU.MOV _ src := src

/- Remaining illegal ops (for which ALU_check is ff) are nops here. -/
| _ dst _ := dst

@[match_simp]
private theorem doALU_MOV_def (x y : value) :
  MOV.doALU64 x y = y :=
by cases x; cases y; refl

@[match_simp]
private theorem doALU_scalar_def (op : ALU) (x y : i64) :
  op.doALU64 (value.scalar x) (value.scalar y) = value.scalar (doALU64_scalar op x y) :=
by cases op; simp only [doALU64]

@[match_simp]
private theorem doALU_pointer_scalar_def (op : ALU) {m} (x y : i64) :
  op.doALU64 (value.pointer m x) (value.scalar y) = op.doALU_pointer_scalar m x y :=
by cases op; simp only [doALU64]

/--
Perform a 32-bit ALU operation by truncating registers to 32 bits and zero-extending
the result back to 64 bits.
-/
@[reducible]
def doALU32_scalar (op : ALU) (x y : i64) : i64 :=
bv.concat (0 : i32) (doALU_scalar op (trunc32 x) (trunc32 y))

@[match_simp]
def doALU32 : ALU → value → value → value
| op (value.scalar x) (value.scalar y) := value.scalar (doALU32_scalar op x y)

/- MOV scalar into uninitialized is okay. -/
| ALU.MOV _ (value.scalar src) := value.scalar $ bv.concat (0 : i32) (trunc32 src)

/- Remaining illegal ops (for which ALU_check is ff) are nops here. -/
| _ dst _ := dst

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

private def repr : JMP → string
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

/- Whether a JMP operation between two operands is allowed. -/
def doJMP_check : JMP → value → value → bool
| _ (value.scalar _) (value.scalar _) := tt
| _ _ _ := ff

/-- Evaluate a JMP condition on two concrete bitvectors. -/
def doJMP_scalar {n : ℕ} : JMP → (fin n → bool) → (fin n → bool) → bool
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

def doJMP : JMP → value → value → bool
| op (value.scalar x) (value.scalar y) := doJMP_scalar op x y
| _ _ _ := ff

/-- Evaluate a 32-bit JMP operation on 64-bit operands taking the lower 32 bits of inputs. -/
@[reducible]
def doJMP32_scalar (op : JMP) (x y : i64) : bool :=
@doJMP_scalar 32 op (trunc32 x) (trunc32 y)

end JMP

/-- Built-in BPF functions recognized by the verifier. -/
@[derive [decidable_eq, inhabited, has_reflect, fintype]]
inductive BPF_FUNC : Type
| get_prandom_u32

namespace BPF_FUNC

private def repr : BPF_FUNC → string
| get_prandom_u32  := "get_prandom_u32"

instance : has_repr BPF_FUNC := ⟨repr⟩

def do_call_check : BPF_FUNC → (reg → value) → bool
| BPF_FUNC.get_prandom_u32 _ := tt

def do_call : BPF_FUNC → oracle → ℕ → (reg → value) → (reg → value)
| BPF_FUNC.get_prandom_u32 o next_rng regs :=
  let regs' : reg → value := λ r, if r ∈ reg.caller_saved then value.uninitialized else regs r,
      return : i64 := o.rng next_rng,
      regs'' : reg → value := function.update regs' reg.R0 (value.scalar return) in
  regs''

end BPF_FUNC

/--
Low-level representation of BPF instructions. In this format, jump offsets are still encoded
as bitvector offsets in the instruction stream. See `cfg.lean` for the higher-level representation
used for analysis.

Note: Unlike most of our bitvector infrastructure, bitvectors in this format have the _MSB_ at
bit index 0, which matches the built-in library Lean has for operations on `vector bool n`, and
simplifies the job of the decoder. When we parse this to the CFG format, we must be careful flip
bit ordering accordingly.
-/
@[derive decidable_eq]
inductive instr : Type
| ALU64_X : ALU → reg → reg → instr
| ALU64_K : ALU → reg → msbvector 32 → instr
| ALU32_X : ALU → reg → reg → instr
| ALU32_K : ALU → reg → msbvector 32 → instr
| JMP_X   : JMP → reg → reg → msbvector 16 → instr
| JMP_K   : JMP → reg → msbvector 32 → msbvector 16 → instr
| STX     : SIZE → reg → reg → msbvector 16 → instr
| CALL    : BPF_FUNC → instr
| Exit    : instr

namespace instr

private def repr' : instr → string
| (ALU64_X op dst src)   := "ALU64_X " ++ repr op ++ " " ++ repr dst ++ " " ++ repr src
| (ALU64_K op dst imm)   := "ALU64_K " ++ repr op ++ " " ++ repr dst ++ " " ++ repr imm
| (ALU32_X op dst src)   := "ALU32_X " ++ repr op ++ " " ++ repr dst ++ " " ++ repr src
| (ALU32_K op dst imm)   := "ALU32_K " ++ repr op ++ " " ++ repr dst ++ " " ++ repr imm
| (JMP_X op dst src off) := "JMP_X " ++ repr op ++ " " ++ repr dst ++ " " ++ repr src ++ " " ++ repr off
| (JMP_K op dst imm off) := "JMP_K " ++ repr op ++ " " ++ repr dst ++ " " ++ repr imm ++ " " ++ repr off
| (STX size dst src off) := "STX " ++ repr size ++ " " ++ repr dst ++ " " ++ repr src ++ " " ++ repr off
| (CALL BPF_FUNC)        := "CALL " ++ repr BPF_FUNC
| Exit                   := "Exit"

instance : has_repr instr := ⟨repr'⟩

end instr
end bpf
