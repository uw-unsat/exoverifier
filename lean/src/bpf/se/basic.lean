/-
Copyright (c) 2021 The UNSAT Group. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luke Nelson, Xi Wang
-/
import ..basic
import .symbolic_value
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
(regs : vector (symvalue β) bpf.nregs)
(next_rng : num)

section impl

variables
  {χ : Type*} {η β γ : Type u}
  [unordered_map η (bpf.cfg.instr η) χ] [decidable_eq η]
  [smt.factory β γ] [smt.extract_factory β γ] [smt.neg_factory β γ] [smt.add_factory β γ]
  [smt.and_factory β γ] [smt.const_factory β γ] [smt.eq_factory β γ] [smt.implies_factory β γ]
  [smt.redor_factory β γ] [smt.not_factory β γ] [smt.or_factory β γ] [smt.var_factory β γ]
  [smt.udiv_factory β γ] [smt.xor_factory β γ] [smt.sub_factory β γ] [smt.ult_factory β γ]
  [smt.mul_factory β γ] [smt.shl_factory β γ] [smt.lshr_factory β γ] [smt.ite_factory β γ]
  [smt.urem_factory β γ]

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

/-- Step symbolic evaluation for an ALU64_X instruction. -/
def step_alu64_x (cfg : CFG χ η) (k : symstate β η → state γ β) (op : ALU) (dst src : reg) (next : η) (s : symstate β η) : state γ β := do
check ← symvalue.doALU_check op (s.regs.nth dst.to_fin) (s.regs.nth src.to_fin),
s' ← assert check s,
val ← symvalue.doALU op (s.regs.nth dst.to_fin) (s.regs.nth src.to_fin),
k {regs        := s.regs.update_nth dst.to_fin val,
   current     := next, ..s'}

/-- Step symbolic evaluation for an ALU64_K instruction. -/
def step_alu64_k (cfg : CFG χ η) (k : symstate β η → state γ β) (op : ALU) (dst : reg) (imm : lsbvector 64) (next : η) (s : symstate β η) : state γ β := do
(const : symvalue β) ← symvalue.mk_scalar imm,
check ← symvalue.doALU_check op (s.regs.nth dst.to_fin) const,
s' ← assert check s,
val ← symvalue.doALU op (s.regs.nth dst.to_fin) const,
k {regs        := s.regs.update_nth dst.to_fin val,
   current     := next, ..s'}

/-- Step symbolic evaluation for a JMP_X instruction. -/
def step_jmp64_x (cfg : CFG χ η) (k : symstate β η → state γ β) (op : JMP) (dst src : reg) (if_true if_false : η) (s : symstate β η) : state γ β := do
check ← symvalue.doJMP_check op (s.regs.nth dst.to_fin) (s.regs.nth src.to_fin),
s' ← assert check s,
cond ← symvalue.doJMP op (s'.regs.nth dst.to_fin) (s'.regs.nth src.to_fin),
ncond ← mk_not cond,
truestate ← assume_ cond s',
true_condition ← k {current := if_true, ..truestate},
falsestate ← assume_ ncond s',
false_condition ← k {current := if_false, ..falsestate},
mk_and true_condition false_condition

/-- Step symbolic evaluation for a JMP_K instruction. -/
def step_jmp64_k (cfg : CFG χ η) (k : symstate β η → state γ β) (op : JMP) (dst : reg) (imm : lsbvector 64) (if_true if_false : η) (s : symstate β η) : state γ β := do
(const : symvalue β) ← symvalue.mk_scalar imm,
check ← symvalue.doJMP_check op (s.regs.nth dst.to_fin) const,
s' ← assert check s,
cond ← symvalue.doJMP op (s'.regs.nth dst.to_fin) const,
ncond ← mk_not cond,
truestate ← assume_ cond s',
true_condition ← k {current := if_true, ..truestate},
falsestate ← assume_ ncond s',
false_condition ← k {current := if_false, ..falsestate},
mk_and true_condition false_condition

def step_exit (cfg : CFG χ η) (k : symstate β η → state γ β) (s : symstate β η) : state γ β := do
(noleak : β) ← mk_const1 (s.regs.nth reg.R0.to_fin).is_scalar,
s ← assert noleak s,
pure s.assertions

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
  | some (instr.Exit) := step_exit cfg k s
  | some (instr.STX size dst src imm next) := die
  | some (instr.CALL func next) := die
  | none := die
  end

/-- Step symbolic evaluation at most "fuel" times. -/
def symeval (cfg : CFG χ η) : ∀ (fuel : ℕ), symstate β η → state γ β
| 0       := infeasible
| (n + 1) := step_symeval cfg (symeval n)

/-- Construct the initial symbolic state from cfg and registers. -/
def initial_symstate (cfg : CFG χ η) (o : erased oracle) : state γ (symstate β η) := do
truthy : β ← mk_true,
pure { assumptions := truthy,
       assertions  := truthy,
       regs        := vector.repeat symvalue.uninitialized bpf.nregs,
       current     := cfg.entry,
       next_rng    := 0 }

/-- Generate verification conditions for the safety of "cfg" given some fuel and initial registers. -/
def vcgen (cfg : CFG χ η) (fuel : ℕ) (o : erased oracle) : state γ β := do
init : symstate β η ← initial_symstate cfg o,
symeval cfg fuel init

end impl
end se
end cfg
end bpf
