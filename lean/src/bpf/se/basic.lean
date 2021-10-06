/-
Copyright (c) 2021 The UNSAT Group. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luke Nelson, Xi Wang
-/
import ..basic
import ..cfg
import smt.factory

namespace bpf
namespace cfg
namespace se

universes u

open bpf bpf.cfg factory.monad factory smt.extract_factory smt.neg_factory smt.add_factory
     smt.and_factory smt.const_factory smt.eq_factory smt.implies_factory smt.redor_factory
     smt.not_factory smt.or_factory smt.var_factory smt.udiv_factory smt.xor_factory
     smt.sub_factory smt.ult_factory smt.ule_factory smt.slt_factory smt.sle_factory
     smt.mul_factory smt.shl_factory smt.lshr_factory smt.ashr_factory smt.ite_factory
open unordered_map

/--
  Symbolic state consists of boolean expressions corresponding to the assertions and assumptions,
  the current label, and a symbolic register set.
-/
structure symstate (β η : Type*) :=
(assumptions assertions : β)
(current : η)
(regs : reg → β)

section impl

variables
  {χ : Type*} {η β γ : Type u}
  [unordered_map η (bpf.cfg.instr η) χ] [decidable_eq η]
  [smt.factory β γ] [smt.extract_factory β γ] [smt.neg_factory β γ] [smt.add_factory β γ]
  [smt.and_factory β γ] [smt.const_factory β γ] [smt.eq_factory β γ] [smt.implies_factory β γ]
  [smt.redor_factory β γ] [smt.not_factory β γ] [smt.or_factory β γ] [smt.var_factory β γ]
  [smt.udiv_factory β γ] [smt.xor_factory β γ] [smt.sub_factory β γ] [smt.ult_factory β γ]
  [smt.mul_factory β γ] [smt.shl_factory β γ] [smt.lshr_factory β γ] [smt.ite_factory β γ]

/-- Add an assertion to symbolic state. -/
def assert (c : β) (s : symstate β η) : state γ (symstate β η) := do
c' ← mk_implies s.assumptions c,
assertions' ← mk_and s.assertions c',
pure {assertions := assertions', ..s}

/-- Add an assumption to symbolic state. -/
def assume_ (c : β) (s : symstate β η) : state γ (symstate β η) := do
c' ← mk_and c s.assumptions,
pure {assumptions := c', ..s}

/-- Construct a false constant in the monad. -/
@[reducible]
def die : state γ β := mk_false

/-- Compute a VC by asserting that the current state is infeasible. -/
def infeasible (s : symstate β η) : state γ β :=
mk_not s.assumptions

/-- Lift a constant function on 64 bits to expressions, losing precision.
    Computationally, this is just `mk_var`. -/
def lift2_denote (f : i64 → i64 → i64) (e₁ e₂ : β) : state γ β :=
mk_var $
(factory.denote γ e₁).bind (λ (v₁ : Σ n, fin n → bool),
  (factory.denote γ e₂).bind (λ (v₂ : Σ n, fin n → bool),
    erased.mk $
      match v₁, v₂ with
      | ⟨64, b₁⟩, ⟨64, b₂⟩ := f b₁ b₂
      | _,        _        := default _
      end))

def doALU : ∀ (op : bpf.ALU) (dst src : β), state γ β
| ALU.MOV  dst src := pure src
| ALU.OR   dst src := mk_or dst src
| ALU.AND  dst src := mk_and dst src
| ALU.NEG  dst _   := mk_neg dst
| ALU.ADD  dst src := mk_add dst src
| ALU.DIV  dst src := mk_udiv dst src
| ALU.XOR  dst src := mk_xor dst src
| ALU.SUB  dst src := mk_sub dst src
| ALU.MUL  dst src := mk_mul dst src
| ALU.LSH  dst src := mk_shl dst src
| ALU.RSH  dst src := mk_lshr dst src
| ALU.ARSH dst src := mk_ashr dst src
| op dst src       := lift2_denote (bpf.ALU.doALU64 op) dst src

def ALU_check : ∀ (op : bpf.ALU) (dst src : β), state γ β
| ALU.DIV  _ src := mk_redor src
| ALU.MOD  _ src := mk_redor src
| ALU.END  _ _   := mk_false
| _        _ _   := mk_true

/-- Step symbolic evaluation for an ALU64_X instruction. -/
def step_alu64_x (cfg : CFG χ η) (k : symstate β η → state γ β) (op : ALU) (dst src : reg) (next : η) (s : symstate β η) : state γ β := do
check ← ALU_check op (s.regs dst) (s.regs src),
s' ← assert check s,
val ← doALU op (s.regs dst) (s.regs src),
k {regs        := function.update s.regs dst val,
   current     := next, ..s'}

/-- Step symbolic evaluation for an ALU64_K instruction. -/
def step_alu64_k (cfg : CFG χ η) (k : symstate β η → state γ β) (op : ALU) (dst : reg) (imm : lsbvector 64) (next : η) (s : symstate β η) : state γ β := do
(const : β) ← mk_const imm,
check ← ALU_check op (s.regs dst) const,
s' ← assert check s,
val ← doALU op (s.regs dst) const,
k {regs        := function.update s.regs dst val,
   current     := next, ..s'}

def doJMP : ∀ (op : bpf.JMP) (dst src : β), state γ β
| JMP.JEQ  dst src := mk_eq dst src
| JMP.JNE  dst src := mk_eq dst src >>= mk_not
| JMP.JSET dst src := mk_and dst src >>= mk_redor
| JMP.JLT  dst src := mk_ult dst src
| JMP.JGT  dst src := mk_ult src dst
| JMP.JLE  dst src := mk_ule dst src
| JMP.JGE  dst src := mk_ule src dst
| JMP.JSLT dst src := mk_slt dst src
| JMP.JSGT dst src := mk_slt src dst
| JMP.JSLE dst src := mk_sle dst src
| JMP.JSGE dst src := mk_sle src dst
-- | op       dst src := mk_var (λ (x : fin 1), bpf.JMP.doJMP op (denote64 dst) (denote64 src))

/-- Step symbolic evaluation for a JMP_X instruction. -/
def step_jmp64_x (cfg : CFG χ η) (k : symstate β η → state γ β) (op : JMP) (dst src : reg) (if_true if_false : η) (s : symstate β η) : state γ β := do
cond ← doJMP op (s.regs dst) (s.regs src),
ncond ← mk_not cond,
truestate ← assume_ cond s,
true_condition ← k {current := if_true, ..truestate},
falsestate ← assume_ ncond s,
false_condition ← k {current := if_false, ..falsestate},
mk_and true_condition false_condition

/-- Step symbolic evaluation for a JMP_K instruction. -/
def step_jmp64_k (cfg : CFG χ η) (k : symstate β η → state γ β) (op : JMP) (dst : reg) (imm : lsbvector 64) (if_true if_false : η) (s : symstate β η) : state γ β := do
(const : β) ← mk_const imm,
cond ← doJMP op (s.regs dst) const,
ncond ← mk_not cond,
truestate ← assume_ cond s,
true_condition ← k {current := if_true, ..truestate},
falsestate ← assume_ ncond s,
false_condition ← k {current := if_false, ..falsestate},
mk_and true_condition false_condition

/-- Run symbolic evaluation for one step (instruction), passing control to continuation k. -/
def step_symeval (cfg : CFG χ η) (k : symstate β η → state γ β) : symstate β η → state γ β :=
λ (s : symstate β η),
  match lookup s.current cfg.code with
  | some (instr.ALU64_X op dst src next) :=
    step_alu64_x cfg k op dst src next s
  | some (instr.ALU64_K op dst imm next) :=
    step_alu64_k cfg k op dst imm next s
  | some (instr.JMP_X op r₁ r₂ if_true if_false) :=
    step_jmp64_x cfg k op r₁ r₂ if_true if_false s
  | some (instr.JMP_K op r₁ imm if_true if_false) :=
    step_jmp64_k cfg k op r₁ imm if_true if_false s
  | some (instr.Exit) := pure s.assertions
  | some (instr.STX size dst src imm next) := die
  | none := die
  end

/-- Step symbolic evaluation at most "fuel" times. -/
def symeval (cfg : CFG χ η) : ∀ (fuel : ℕ), symstate β η → state γ β
| 0       := infeasible
| (n + 1) := step_symeval cfg (symeval n)

protected def initial_regs : ∀ {n : ℕ}, erased (vector i64 n) → state γ (vector β n)
| 0 _ := pure vector.nil
| (n + 1) regs := do
  (x : β) ← mk_var $ regs.map vector.head,
  xs ← @initial_regs n $ regs.map vector.tail,
  pure $ vector.cons x xs

/-- Construct the initial symbolic state from cfg and registers. -/
def initial_symstate (cfg : CFG χ η) (regs' : erased (vector i64 nregs)) : state γ (symstate β η) := do
truthy : β ← mk_true,
(regs : vector β nregs) ← se.initial_regs regs',
pure { assumptions := truthy,
       assertions  := truthy,
       regs        := bpf.reg.of_vector regs,
       current     := cfg.entry }

/-- Generate verification conditions for the safety of "cfg" given some fuel and initial registers. -/
def vcgen (cfg : CFG χ η) (fuel : ℕ) (regs : erased (vector i64 nregs)) : state γ β := do
init : symstate β η ← initial_symstate cfg regs,
symeval cfg fuel init

end impl
end se
end cfg
end bpf
