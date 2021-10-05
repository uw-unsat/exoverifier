/-
Copyright (c) 2021 The UNSAT Group. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luke Nelson, Xi Wang
-/
import bpf.basic
import data.domain.basic
import data.domain.bv

/-!
# Abstract domains for BPF registers
-/

namespace absint

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
open has_γ abstr_top abstr_le abstr_join

abbreviation aregs (β : Type) := vector β bpf.nregs

def interpret (abs : aregs β) : bpf.reg → β :=
λ k, (abs.nth k.to_fin)

instance : has_γ (bpf.reg → bpf.i64) (aregs β) :=
{ γ := λ (l : aregs β) (f : bpf.reg → bpf.i64),
    ∀ k, γ (interpret l k) (f k),
  abstract := λ (f : bpf.reg → bpf.i64),
    (fin_enum.to_vector bpf.reg).map (abstract ∘ f),
  abstract_correct := by {
    intros f r,
    simp only [interpret, vector.nth_map, bpf.reg.to_fin, fin_enum.nth_to_vector],
    apply abstract_correct } }

instance : has_le (aregs β) :=
⟨ λ a b, ∀ k, interpret a k ≤ interpret b k ⟩

instance : abstr_le (bpf.reg → bpf.i64) (aregs β) :=
{ dec_le     := infer_instance,
  le_correct := by {
    intros x y h₁ f h₂ r,
    apply le_correct (h₁ r) (h₂ r) } }

instance : abstr_top (bpf.reg → bpf.i64) (aregs β) :=
{ top := vector.repeat ⊤ _,
  top_correct := by {
    intros _ _,
    simp only [interpret, vector.nth_repeat],
    apply top_correct } }

instance : abstr_join (bpf.reg → bpf.i64) (aregs β) (aregs β) :=
{ join := λ x y, vector.map₂ join x y,
  join_correct := by {
    rintros x y f h₁ r,
    simp only [interpret, vector.nth_map₂],
    apply join_correct,
    cases h₁,
    { left,
      exact h₁ r },
    { right,
      exact h₁ r } } }

/-- Test whether `reg` can be `val`. -/
def test_reg (abs : aregs β) (reg : bpf.reg) (val : bpf.i64) : bool :=
γ (interpret abs reg) val

def test_reg_neq (reg : bpf.reg) (val : bpf.i64) :
  abstr_unary_test (bpf.reg → bpf.i64) (aregs β) (λ cregs, cregs reg ≠ val) :=
{ test       := λ (l : aregs β), !to_bool (γ (interpret l reg) val),
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
  abstr_unary_transfer (bpf.reg → bpf.i64) (aregs β)
    (λ cregs, function.update cregs dst (bpf.ALU.doALU op (cregs dst) (cregs src))) :=
{ op      := λ (l : aregs β), l.update_nth dst.to_fin ((transfer_ALU op).op (interpret l dst) (interpret l src)),
  correct := by {
    intros _ _ h₁ r,
    simp only [function.update],
    split_ifs with h,
    { subst h,
      simp only [interpret, option.get_or_else_some, vector.nth_update_nth_same],
      exact (transfer_ALU op).correct (h₁ r) (h₁ src) },
    { simp only [interpret],
      rw [vector.nth_update_nth_of_ne _],
      exact h₁ r,
      contrapose! h,
      symmetry,
      apply bpf.reg.to_fin_inj h } } }

def do_alu_imm (op : bpf.ALU) (dst : bpf.reg) (imm : lsbvector 64) :
  abstr_unary_transfer (bpf.reg → bpf.i64) (aregs β)
    (λ cregs, function.update cregs dst (bpf.ALU.doALU op (cregs dst) imm.nth)) :=
{ op      := λ (l : aregs β), l.update_nth dst.to_fin ((transfer_ALU op).op (interpret l dst) (abstract imm.nth)),
  correct := by {
    intros _ _ h₁ r,
    simp only [function.update],
    split_ifs with h,
    { subst h,
      simp only [interpret, option.get_or_else_some, vector.nth_update_nth_same],
      exact (transfer_ALU op).correct (h₁ r) (abstract_correct _) },
    { simp only [interpret],
      rw [vector.nth_update_nth_of_ne _],
      exact h₁ r,
      contrapose! h,
      symmetry,
      apply bpf.reg.to_fin_inj h } } }

/-- Abstract transfer function for ALU operations. -/
def transfer_JMP : ∀ (op : bpf.JMP), abstr_binary_inversion bpf.i64 β (with_bot β) (λ x y, bpf.JMP.doJMP op x y = tt)
| bpf.JMP.JEQ := by {
  convert abstr_meet.invert_equality,
  simp only [bpf.JMP.doJMP, to_bool_iff],
  apply_instance }
| bpf.JMP.JLT := by {
  convert bv_abstr.lt,
  simp only [bpf.JMP.doJMP, to_bool_iff] }
| bpf.JMP.JGT := by {
  convert bv_abstr.gt,
  simp only [bpf.JMP.doJMP, to_bool_iff] }
| bpf.JMP.JLE := by {
  convert bv_abstr.le,
  simp only [bpf.JMP.doJMP, to_bool_iff] }
| bpf.JMP.JGE := by {
  convert bv_abstr.ge,
  simp only [bpf.JMP.doJMP, to_bool_iff] }
| _ := abstr_binary_inversion.trivial

def invert_jmp_tt (op : bpf.JMP) (dst src : bpf.reg) :
  abstr_unary_inversion (bpf.reg → bpf.i64) (aregs β) (with_bot (aregs β))
    (λ (cregs : bpf.reg → bpf.i64), bpf.JMP.doJMP op (cregs dst) (cregs src) = tt) :=
{ inv := λ (l : aregs β),
    (let z := (transfer_JMP op).inv (interpret l dst) (interpret l src) in do
      dst' ← z.1,
      src' ← z.2,
      pure $ (l.update_nth dst.to_fin dst').update_nth src.to_fin src'),
  correct := by {
    intros regs regs' h₁ jmp_eq,
    simp only,
    have h₃ := (transfer_JMP op).correct (h₁ dst) (h₁ src) jmp_eq,
    cases ((transfer_JMP op).inv (interpret regs' dst) (interpret regs' src)).1 with dst',
    { rcases h₃ with ⟨⟨⟩, -⟩ },
    cases ((transfer_JMP op).inv (interpret regs' dst) (interpret regs' src)).2 with src',
    { rcases h₃ with ⟨-, ⟨⟩⟩ },
    simp only [option.some_bind],
    intros r,
    simp only [interpret],
    by_cases h₄ : src.to_fin = r.to_fin,
    { have h₄' := bpf.reg.to_fin_inj h₄,
      subst h₄',
      rw [vector.nth_update_nth_same],
      rcases h₃ with ⟨-, h₃⟩,
      exact h₃ },
    rw [vector.nth_update_nth_of_ne h₄],
    by_cases h₅ : dst.to_fin = r.to_fin,
    { have h₅' := bpf.reg.to_fin_inj h₅,
      subst h₅',
      rw [vector.nth_update_nth_same],
      rcases h₃ with ⟨h₃, -⟩,
      exact h₃ },
    rw [vector.nth_update_nth_of_ne h₅],
    exact h₁ r } }

instance : regs_abstr (aregs β) :=
{ do_alu         := do_alu,
  do_alu_imm     := do_alu_imm,
  invert_jmp_tt  := invert_jmp_tt,
  test_reg_neq   := test_reg_neq }

end nonrelational
end absint
