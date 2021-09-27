/-
Copyright (c) 2021 The UNSAT Group. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luke Nelson, Xi Wang
-/
import bpf.basic
import data.domain.basic

/-!
# Abstract domains for BPF registers
-/

/--
An abstraction of BPF registers.
-/
class regs_abstr (α : Type*) extends
  has_γ (bpf.reg → bpf.i64) α,
  abstr_top (bpf.reg → bpf.i64) α,
  abstr_le (bpf.reg → bpf.i64) α,
  abstr_join (bpf.reg → bpf.i64) α α :=

-- Do a reg-reg ALU op.
(do_alu (op : bpf.ALU) (dst src : bpf.reg) :
  abstr_unary_transfer (bpf.reg → bpf.i64) α
    (λ cregs, function.update cregs dst (bpf.ALU.doALU op (cregs dst) (cregs src))))

-- Do an ALU op with an immediate.
(do_alu_imm (op : bpf.ALU) (dst : bpf.reg) (imm : lsbvector 64) :
  abstr_unary_transfer (bpf.reg → bpf.i64) α
    (λ cregs, function.update cregs dst (bpf.ALU.doALU op (cregs dst) imm.nth)))

-- Invert a reg/reg JMP op whose condition is true
(invert_jmp_tt (op : bpf.JMP) (dst src : bpf.reg) :
  abstr_unary_inversion (bpf.reg → bpf.i64) α (with_bot α)
    (λ (cregs : bpf.reg → bpf.i64), bpf.JMP.doJMP op (cregs dst) (cregs src) = tt))

-- Test if a register `reg` cannot be equal to `val`.
(test_reg_neq (reg : bpf.reg) (val : bpf.i64) :
  abstr_unary_test (bpf.reg → bpf.i64) α
    (λ cregs, cregs reg ≠ val))

namespace nonrelational

variables {β : Type} [bv_abstr 64 β]
open abstr_top has_γ

/-- Test whether `reg` can be `val`. -/
def test_reg (abs : bpf.reg → β) (reg : bpf.reg) (val : bpf.i64) : bool :=
γ (abs reg) val

def test_reg_neq (reg : bpf.reg) (val : bpf.i64) :
  abstr_unary_test (bpf.reg → bpf.i64) (bpf.reg → β) (λ cregs, cregs reg ≠ val) :=
{ test       := λ aregs, !to_bool (γ (aregs reg) val),
  test_sound := by {
    intros _ _ test_tt gamma,
    simp only [bnot_eq_true_eq_eq_ff, bool.to_bool_not, to_bool_ff_iff] at test_tt ⊢,
    contrapose! test_tt,
    subst test_tt,
    apply gamma } }

/-- Abstract transfer function for ALU operations. -/
def transfer_ALU : ∀ (op : bpf.ALU), abstr_binary_transfer bpf.i64 β β (bpf.ALU.doALU64 op)
| bpf.ALU.ADD := bv_abstr.add
| bpf.ALU.AND := bv_abstr.and
| bpf.ALU.OR  := bv_abstr.or
| bpf.ALU.XOR := bv_abstr.xor
| bpf.ALU.MOV :=
  { op      := λ _ y, y,
    correct := by { intros, assumption } }
| _ :=
  { op      := λ _ _, ⊤,
    correct := by {
      intros,
      apply top_correct } }

def do_alu (op : bpf.ALU) (dst src : bpf.reg) :
  abstr_unary_transfer (bpf.reg → bpf.i64) (bpf.reg → β)
    (λ cregs, function.update cregs dst (bpf.ALU.doALU op (cregs dst) (cregs src))) :=
{ op      := λ aregs, function.update aregs dst ((transfer_ALU op).op (aregs dst) (aregs src)),
  correct := by {
    intros _ _ h₁ r,
    simp only [function.update],
    split_ifs with h,
    { subst h,
      exact (transfer_ALU op).correct (h₁ r) (h₁ src) },
    { exact h₁ r } } }

def do_alu_imm (op : bpf.ALU) (dst : bpf.reg) (imm : lsbvector 64) :
  abstr_unary_transfer (bpf.reg → bpf.i64) (bpf.reg → β)
    (λ cregs, function.update cregs dst (bpf.ALU.doALU op (cregs dst) imm.nth)) :=
{ op      := λ aregs, function.update aregs dst ((transfer_ALU op).op (aregs dst) (abstract imm.nth)),
  correct := by {
    intros _ _ h₁ r,
    simp only [function.update],
    split_ifs with h,
    { subst h,
      exact (transfer_ALU op).correct (h₁ r) (abstract_correct _) },
    { exact h₁ r } } }

def invert_jmp_tt (op : bpf.JMP) (dst src : bpf.reg) :
  abstr_unary_inversion (bpf.reg → bpf.i64) (bpf.reg → β) (with_bot (bpf.reg → β))
    (λ (cregs : bpf.reg → bpf.i64), bpf.JMP.doJMP op (cregs dst) (cregs src) = tt) :=
{ inv     := λ x, some x,
  correct := by {
    intros _ _ h₁ h₂,
    exact h₁ } }

instance : regs_abstr (bpf.reg → β) :=
{ do_alu         := do_alu,
  do_alu_imm     := do_alu_imm,
  invert_jmp_tt  := invert_jmp_tt,
  test_reg_neq   := test_reg_neq }

-- /-- Reify registers from meta lean to regular lean. -/
-- instance (β' : Type) [has_serialize β β'] : has_serialize (bpf.reg → β) (list β') :=
-- ⟨ λ (regs : bpf.reg → β), (serialize regs).map has_serialize.serialize,
--   λ (l : list β'), deserialize (l.map has_serialize.deserialize) ⟩

end nonrelational
