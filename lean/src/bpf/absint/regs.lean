/-
Copyright (c) 2021 The UNSAT Group. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luke Nelson, Xi Wang
-/
import .value
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
  has_γ (bpf.reg → bpf.value) α,
  abstr_top (bpf.reg → bpf.value) α,
  abstr_le (bpf.reg → bpf.value) α,
  abstr_join (bpf.reg → bpf.value) α α :=

-- Do a reg-reg ALU op.
(do_alu (op : bpf.ALU) (dst src : bpf.reg) :
  abstr_unary_transfer (bpf.reg → bpf.value) α α
    (λ cregs, function.update cregs dst (bpf.ALU.doALU op (cregs dst) (cregs src))))

-- Check if an ALU op is legal.
(do_alu_check (op : bpf.ALU) (dst src : bpf.reg) :
  abstr_unary_test (bpf.reg → bpf.value) α
    (λ cregs, bpf.ALU.doALU_check op (cregs dst) (cregs src)))

-- Do an ALU op with an immediate.
(do_alu_imm (op : bpf.ALU) (dst : bpf.reg) (imm : lsbvector 64) :
  abstr_unary_transfer (bpf.reg → bpf.value) α α
    (λ cregs, function.update cregs dst (bpf.ALU.doALU op (cregs dst) (bpf.value.scalar imm.nth))))

-- Check if an ALU op is legal.
(do_alu_imm_check (op : bpf.ALU) (dst : bpf.reg) (imm : lsbvector 64) :
  abstr_unary_test (bpf.reg → bpf.value) α
    (λ cregs, bpf.ALU.doALU_check op (cregs dst) (bpf.value.scalar imm.nth)))

-- Check if a JMP is legal on some operands.
(do_jmp_check (op : bpf.JMP) (dst src : bpf.reg) :
  abstr_unary_test (bpf.reg → bpf.value) α
    (λ cregs, bpf.JMP.doJMP_check op (cregs dst) (cregs src)))

-- Check if a JMP is legal on some operands.
(do_jmp_imm_check (op : bpf.JMP) (dst : bpf.reg) (imm : lsbvector 64) :
  abstr_unary_test (bpf.reg → bpf.value) α
    (λ cregs, bpf.JMP.doJMP_check op (cregs dst) (bpf.value.scalar imm.nth)))

-- Invert a reg/reg JMP op whose condition is true
(invert_jmp_tt (op : bpf.JMP) (dst src : bpf.reg) :
  abstr_unary_inversion (bpf.reg → bpf.value) α (with_bot α)
    (λ (cregs : bpf.reg → bpf.value), bpf.JMP.doJMP op (cregs dst) (cregs src) = tt))

(is_scalar (r : bpf.reg) :
  abstr_unary_test (bpf.reg → bpf.value) α
    (λ (cregs : bpf.reg → bpf.value), (cregs r).is_scalar))

namespace nonrelational

variables {β : Type} [value_abstr β]
open has_γ abstr_top abstr_le abstr_join

abbreviation aregs (β : Type) := vector β bpf.nregs

private def interpret (abs : aregs β) : bpf.reg → β :=
λ k, (abs.nth k.to_fin)

instance : has_γ (bpf.reg → bpf.value) (aregs β) :=
{ γ := λ (l : aregs β) (f : bpf.reg → bpf.value),
    ∀ k, γ (interpret l k) (f k),
  abstract := λ (f : bpf.reg → bpf.value),
    (fin_enum.to_vector bpf.reg).map (abstract ∘ f),
  abstract_correct := by {
    intros f r,
    simp only [interpret, vector.nth_map, bpf.reg.to_fin, fin_enum.nth_to_vector],
    apply abstract_correct } }

instance : has_le (aregs β) :=
⟨ λ a b, ∀ k, interpret a k ≤ interpret b k ⟩

instance : abstr_le (bpf.reg → bpf.value) (aregs β) :=
{ dec_le     := infer_instance,
  le_correct := by {
    intros x y h₁ f h₂ r,
    apply le_correct (h₁ r) (h₂ r) } }

instance : abstr_top (bpf.reg → bpf.value) (aregs β) :=
{ top := vector.repeat ⊤ _,
  top_correct := by {
    intros _ _,
    simp only [interpret, vector.nth_repeat],
    apply top_correct } }

instance : abstr_join (bpf.reg → bpf.value) (aregs β) (aregs β) :=
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

private def do_alu_check (op : bpf.ALU) (dst src : bpf.reg) :
  abstr_unary_test (bpf.reg → bpf.value) (aregs β)
    (λ (cregs : bpf.reg → bpf.value), op.doALU_check (cregs dst) (cregs src)) :=
{ test := λ (l : aregs β), (value_abstr.doALU_check op).test (interpret l dst) (interpret l src),
  test_sound := by {
    intros _ _ h₁ h₂,
    apply (value_abstr.doALU_check op).test_sound h₁ (h₂ _) (h₂ _) } }

private def do_alu_imm_check (op : bpf.ALU) (dst : bpf.reg) (imm : lsbvector 64) :
  abstr_unary_test (bpf.reg → bpf.value) (aregs β)
    (λ (cregs : bpf.reg → bpf.value), op.doALU_check (cregs dst) (bpf.value.scalar imm.nth)) :=
{ test := λ (l : aregs β), (value_abstr.doALU_check op).test (interpret l dst) (abstract (bpf.value.scalar imm.nth)),
  test_sound := by {
    intros _ _ h₁ h₂,
    apply (value_abstr.doALU_check op).test_sound h₁ (h₂ _) _,
    apply has_γ.abstract_correct } }

private def do_alu (op : bpf.ALU) (dst src : bpf.reg) :
  abstr_unary_transfer (bpf.reg → bpf.value) (aregs β) (aregs β)
    (λ cregs, function.update cregs dst (bpf.ALU.doALU op (cregs dst) (cregs src))) :=
{ op      := λ (l : aregs β), l.update_nth dst.to_fin ((value_abstr.doALU op).op (interpret l dst) (interpret l src)),
  correct := by {
    intros _ _ h₁ r,
    simp only [function.update],
    split_ifs with h,
    { subst h,
      simp only [interpret, option.get_or_else_some, vector.nth_update_nth_same],
      exact (value_abstr.doALU op).correct (h₁ r) (h₁ src) },
    { simp only [interpret],
      rw [vector.nth_update_nth_of_ne _],
      exact h₁ r,
      contrapose! h,
      symmetry,
      apply bpf.reg.to_fin_inj h } } }

private def do_alu_imm (op : bpf.ALU) (dst : bpf.reg) (imm : lsbvector 64) :
  abstr_unary_transfer (bpf.reg → bpf.value) (aregs β) (aregs β)
    (λ cregs, function.update cregs dst (bpf.ALU.doALU op (cregs dst) (bpf.value.scalar imm.nth))) :=
{ op      := λ (l : aregs β), l.update_nth dst.to_fin ((value_abstr.doALU op).op (interpret l dst) (abstract (bpf.value.scalar imm.nth))),
  correct := by {
    intros _ _ h₁ r,
    simp only [function.update],
    split_ifs with h,
    { subst h,
      simp only [interpret, option.get_or_else_some, vector.nth_update_nth_same],
      exact (value_abstr.doALU op).correct (h₁ r) (abstract_correct _) },
    { simp only [interpret],
      rw [vector.nth_update_nth_of_ne _],
      exact h₁ r,
      contrapose! h,
      symmetry,
      apply bpf.reg.to_fin_inj h } } }

private def do_jmp_check (op : bpf.JMP) (dst src : bpf.reg) :
  abstr_unary_test (bpf.reg → bpf.value) (aregs β)
    (λ (cregs : bpf.reg → bpf.value), op.doJMP_check (cregs dst) (cregs src)) :=
{ test := λ (l : aregs β), (value_abstr.doJMP_check op).test (interpret l dst) (interpret l src),
  test_sound := by {
    intros _ _ h₁ h₂,
    apply (value_abstr.doJMP_check op).test_sound h₁ (h₂ _) (h₂ _) } }

private def do_jmp_imm_check (op : bpf.JMP) (dst : bpf.reg) (imm : lsbvector 64) :
  abstr_unary_test (bpf.reg → bpf.value) (aregs β)
    (λ (cregs : bpf.reg → bpf.value), op.doJMP_check (cregs dst) (bpf.value.scalar imm.nth)) :=
{ test := λ (l : aregs β), (value_abstr.doJMP_check op).test (interpret l dst) (abstract (bpf.value.scalar imm.nth)),
  test_sound := by {
    intros _ _ h₁ h₂,
    apply (value_abstr.doJMP_check op).test_sound h₁ (h₂ _) _,
    apply has_γ.abstract_correct } }

private def invert_jmp_tt (op : bpf.JMP) (dst src : bpf.reg) :
  abstr_unary_inversion (bpf.reg → bpf.value) (aregs β) (with_bot (aregs β))
    (λ (cregs : bpf.reg → bpf.value), bpf.JMP.doJMP op (cregs dst) (cregs src) = tt) :=
{ inv := λ (l : aregs β),
    (let z := (value_abstr.doJMP_tt op).inv (interpret l dst) (interpret l src) in do
      dst' ← z.1,
      src' ← z.2,
      pure $ (l.update_nth dst.to_fin dst').update_nth src.to_fin src'),
  correct := by {
    intros regs regs' h₁ jmp_eq,
    simp only,
    have h₃ := (value_abstr.doJMP_tt op).correct (h₁ dst) (h₁ src) jmp_eq,
    cases ((value_abstr.doJMP_tt op).inv (interpret regs' dst) (interpret regs' src)).1 with dst',
    { rcases h₃ with ⟨⟨⟩, -⟩ },
    cases ((value_abstr.doJMP_tt op).inv (interpret regs' dst) (interpret regs' src)).2 with src',
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

private def is_scalar (r : bpf.reg) :
  abstr_unary_test (bpf.reg → bpf.value) (aregs β)
    (λ (cregs : bpf.reg → bpf.value), to_bool (cregs r).is_scalar) :=
{ test := λ (l : aregs β), value_abstr.is_scalar.test (interpret l r),
  test_sound := by {
    intros _ _ h₁ h₂,
    apply value_abstr.is_scalar.test_sound h₁ (h₂ _) } }

instance : regs_abstr (aregs β) :=
{ do_alu           := do_alu,
  do_alu_check     := do_alu_check,
  do_alu_imm       := do_alu_imm,
  do_alu_imm_check := do_alu_imm_check,
  do_jmp_imm_check := do_jmp_imm_check,
  invert_jmp_tt    := invert_jmp_tt,
  is_scalar        := is_scalar,
  do_jmp_check     := do_jmp_check }

end nonrelational
end absint
