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
(do_alu64 (op : bpf.ALU) (dst src : bpf.reg) :
  abstr_unary_transfer
    (λ (cregs : bpf.reg → bpf.value), function.update cregs dst (bpf.ALU.doALU64 op (cregs dst) (cregs src)))
    α α)

-- Check if an ALU op is legal.
(do_alu64_check (op : bpf.ALU) (dst src : bpf.reg) :
  abstr_unary_test (λ (cregs : bpf.reg → bpf.value), bpf.ALU.doALU64_check op (cregs dst) (cregs src)) α)

-- Do an ALU op with an immediate.
(do_alu64_imm (op : bpf.ALU) (dst : bpf.reg) (imm : lsbvector 64) :
  abstr_unary_transfer
    (λ (cregs : bpf.reg → bpf.value), function.update cregs dst (bpf.ALU.doALU64 op (cregs dst) (bpf.value.scalar imm.nth)))
    α α)

-- Check if an ALU op is legal.
(do_alu64_imm_check (op : bpf.ALU) (dst : bpf.reg) (imm : lsbvector 64) :
  abstr_unary_test (λ (cregs : bpf.reg → bpf.value), bpf.ALU.doALU64_check op (cregs dst) (bpf.value.scalar imm.nth)) α)

-- Check if a JMP is legal on some operands.
(do_jmp64_check (op : bpf.JMP) (dst src : bpf.reg) :
  abstr_unary_test (λ (cregs : bpf.reg → bpf.value), bpf.JMP.doJMP64_check op (cregs dst) (cregs src)) α)

-- Check if a JMP is legal on some operands.
(do_jmp64_imm_check (op : bpf.JMP) (dst : bpf.reg) (imm : lsbvector 64) :
  abstr_unary_test (λ (cregs : bpf.reg → bpf.value), bpf.JMP.doJMP64_check op (cregs dst) (bpf.value.scalar imm.nth)) α)

-- Invert a reg/reg JMP op whose condition is true
(invert_jmp64_tt (op : bpf.JMP) (dst src : bpf.reg) :
  abstr_unary_inversion (λ (cregs : bpf.reg → bpf.value), bpf.JMP.doJMP64 op (cregs dst) (cregs src) = tt)
    α (with_bot α))

(is_scalar (r : bpf.reg) :
  abstr_unary_test (λ (cregs : bpf.reg → bpf.value), (cregs r).is_scalar) α)

(do_call_check (func : bpf.BPF_FUNC) :
  abstr_unary_test (λ (cregs : bpf.reg → bpf.value), func.do_call_check cregs) α)

(do_call (func : bpf.BPF_FUNC) :
  abstr_unary_relation (λ pre post, ∃ (o : bpf.oracle) (next_rng : ℕ), post = func.do_call o next_rng pre)
    α α)

(const (rs : bpf.reg → bpf.value) :
  abstr_nullary_relation (= rs) α)

namespace nonrelational

variables {β : Type} [value_abstr β]
open has_γ abstr_top abstr_le abstr_join

abbreviation aregs (β : Type) := vector β bpf.nregs

private def interpret (abs : aregs β) : bpf.reg → β :=
λ k, (abs.nth k.to_fin)

instance : has_γ (bpf.reg → bpf.value) (aregs β) :=
{ γ := λ (l : aregs β) (f : bpf.reg → bpf.value),
    ∀ k, γ (interpret l k) (f k) }

private def const (rs : bpf.reg → bpf.value) :
  abstr_nullary_relation (= rs) (aregs β) :=
{ op := (fin_enum.to_vector bpf.reg).map (λ r, (value_abstr.const (rs r)).op),
  correct := by {
    intros _ h r,
    subst h,
    simp only [interpret, vector.nth_map, bpf.reg.to_fin],
    apply (value_abstr.const _).correct,
    simp only [fin_enum.nth_to_vector] } }

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

private def do_alu64_check (op : bpf.ALU) (dst src : bpf.reg) :
  abstr_unary_test
    (λ (cregs : bpf.reg → bpf.value), op.doALU64_check (cregs dst) (cregs src))
    (aregs β) :=
{ test := λ (l : aregs β), (value_abstr.doALU64_check op).test (interpret l dst) (interpret l src),
  test_sound := by {
    intros _ _ h₁ h₂,
    apply (value_abstr.doALU64_check op).test_sound h₁ (h₂ _) (h₂ _) } }

private def do_alu64_imm_check (op : bpf.ALU) (dst : bpf.reg) (imm : lsbvector 64) :
  abstr_unary_test
    (λ (cregs : bpf.reg → bpf.value), op.doALU64_check (cregs dst) (bpf.value.scalar imm.nth))
    (aregs β) :=
{ test := λ (l : aregs β), (value_abstr.doALU64_check op).test (interpret l dst) (value_abstr.const (bpf.value.scalar imm.nth)).op,
  test_sound := by {
    intros _ _ h₁ h₂,
    apply (value_abstr.doALU64_check op).test_sound h₁ (h₂ _) _,
    apply (value_abstr.const _).correct rfl } }

private def do_alu64 (op : bpf.ALU) (dst src : bpf.reg) :
  abstr_unary_transfer
    (λ (cregs : bpf.reg → bpf.value), function.update cregs dst (bpf.ALU.doALU64 op (cregs dst) (cregs src)))
    (aregs β) (aregs β) :=
{ op      := λ (l : aregs β), l.update_nth dst.to_fin ((value_abstr.doALU64 op).op (interpret l dst) (interpret l src)),
  correct := by {
    intros _ _ _ h₁ h r,
    subst h,
    simp only [function.update],
    split_ifs with h,
    { subst h,
      simp only [interpret, option.get_or_else_some, vector.nth_update_nth_same],
      exact (value_abstr.doALU64 op).correct (h₁ r) (h₁ src) rfl },
    { simp only [interpret],
      rw [vector.nth_update_nth_of_ne (bpf.reg.to_fin_ne_of_ne (ne.symm h))],
      exact h₁ r } } }

private def do_alu64_imm (op : bpf.ALU) (dst : bpf.reg) (imm : lsbvector 64) :
  abstr_unary_transfer
    (λ (cregs : bpf.reg → bpf.value), function.update cregs dst (bpf.ALU.doALU64 op (cregs dst) (bpf.value.scalar imm.nth)))
    (aregs β) (aregs β) :=
{ op      := λ (l : aregs β), l.update_nth dst.to_fin ((value_abstr.doALU64 op).op (interpret l dst) (value_abstr.const (bpf.value.scalar imm.nth)).op),
  correct := by {
    intros _ _ _ h₁ h r,
    subst h,
    simp only [function.update],
    split_ifs with h,
    { subst h,
      simp only [interpret, option.get_or_else_some, vector.nth_update_nth_same],
      exact (value_abstr.doALU64 op).correct (h₁ r) ((value_abstr.const _).correct rfl) rfl },
    { simp only [interpret],
      rw [vector.nth_update_nth_of_ne (bpf.reg.to_fin_ne_of_ne (ne.symm h))],
      exact h₁ r } } }

private def do_jmp64_check (op : bpf.JMP) (dst src : bpf.reg) :
  abstr_unary_test
    (λ (cregs : bpf.reg → bpf.value), op.doJMP64_check (cregs dst) (cregs src))
    (aregs β) :=
{ test := λ (l : aregs β), (value_abstr.doJMP64_check op).test (interpret l dst) (interpret l src),
  test_sound := by {
    intros _ _ h₁ h₂,
    apply (value_abstr.doJMP64_check op).test_sound h₁ (h₂ _) (h₂ _) } }

private def do_jmp64_imm_check (op : bpf.JMP) (dst : bpf.reg) (imm : lsbvector 64) :
  abstr_unary_test
    (λ (cregs : bpf.reg → bpf.value), op.doJMP64_check (cregs dst) (bpf.value.scalar imm.nth))
    (aregs β) :=
{ test := λ (l : aregs β), (value_abstr.doJMP64_check op).test (interpret l dst) (value_abstr.const (bpf.value.scalar imm.nth)).op,
  test_sound := by {
    intros _ _ h₁ h₂,
    apply (value_abstr.doJMP64_check op).test_sound h₁ (h₂ _) _,
    apply (value_abstr.const _).correct rfl } }

private def invert_jmp64_tt (op : bpf.JMP) (dst src : bpf.reg) :
  abstr_unary_inversion
    (λ (cregs : bpf.reg → bpf.value), bpf.JMP.doJMP64 op (cregs dst) (cregs src) = tt)
    (aregs β) (with_bot (aregs β)) :=
{ inv := λ (l : aregs β),
    (let z := (value_abstr.doJMP64_tt op).inv (interpret l dst) (interpret l src) in do
      dst' ← z.1,
      src' ← z.2,
      pure $ (l.update_nth dst.to_fin dst').update_nth src.to_fin src'),
  correct := by {
    intros regs regs' h₁ jmp_eq,
    simp only,
    have h₃ := (value_abstr.doJMP64_tt op).correct (h₁ dst) (h₁ src) jmp_eq,
    cases ((value_abstr.doJMP64_tt op).inv (interpret regs' dst) (interpret regs' src)).1 with dst',
    { rcases h₃ with ⟨⟨⟩, -⟩ },
    cases ((value_abstr.doJMP64_tt op).inv (interpret regs' dst) (interpret regs' src)).2 with src',
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
  abstr_unary_test
    (λ (cregs : bpf.reg → bpf.value), (cregs r).is_scalar)
    (aregs β) :=
{ test := λ (l : aregs β), value_abstr.is_scalar.test (interpret l r),
  test_sound := by {
    intros _ _ h₁ h₂,
    apply value_abstr.is_scalar.test_sound h₁ (h₂ _) } }

private def do_call (func : bpf.BPF_FUNC) :
  abstr_unary_relation
    (λ (pre post : bpf.reg → bpf.value), ∃ (o : bpf.oracle) (next_rng : ℕ), post = func.do_call o next_rng pre)
    (aregs β) (aregs β) :=
{ op := λ (l : aregs β),
    let l₁ := list.foldl (λ (l' : aregs β) (r : bpf.reg), l'.update_nth r.to_fin (value_abstr.const bpf.value.uninitialized).op) l bpf.reg.caller_saved in
    l₁.update_nth bpf.reg.R0.to_fin value_abstr.unknown_scalar.op,
  correct := by {
    intros _ _ _ h₁ h r,
    rcases h with ⟨o, next_rng, h⟩,
    subst h,
    cases func,
    simp only [bpf.BPF_FUNC.do_call, bpf.reg.caller_saved, list.mem_cons_iff, list.foldl_cons, list.foldl_nil, list.mem_singleton, list.foldl, interpret],
    cases r; simp [vector.nth_update_nth_eq_if],
    case R0 {
      apply value_abstr.unknown_scalar.correct,
      refine ⟨_, rfl⟩ },
    case R1 {
      apply (value_abstr.const _).correct rfl },
    case R2 {
      apply (value_abstr.const _).correct rfl },
    case R3 {
      apply (value_abstr.const _).correct rfl },
    case R4 {
      apply (value_abstr.const _).correct rfl },
    case R5 {
      apply (value_abstr.const _).correct rfl },
    case R6 {
      exact h₁ _ },
    case R7 {
      exact h₁ _ },
    case R8 {
      exact h₁ _ },
    case R9 {
      exact h₁ _ },
    case FP {
      exact h₁ _ },
    case AX {
      exact h₁ _ } } }

private def do_call_check (func : bpf.BPF_FUNC) :
  abstr_unary_test (λ (cregs : bpf.reg → bpf.value), func.do_call_check cregs) (aregs β) :=
{ test := λ _, tt,
  test_sound := by {
    intros, cases func,
    simp only [bpf.BPF_FUNC.do_call_check, coe_sort_tt] } }

instance : regs_abstr (aregs β) :=
{ const              := const,
  do_alu64           := do_alu64,
  do_call            := do_call,
  do_call_check      := do_call_check,
  do_alu64_check     := do_alu64_check,
  do_alu64_imm       := do_alu64_imm,
  do_alu64_imm_check := do_alu64_imm_check,
  do_jmp64_imm_check := do_jmp64_imm_check,
  invert_jmp64_tt    := invert_jmp64_tt,
  is_scalar          := is_scalar,
  do_jmp64_check     := do_jmp64_check }

end nonrelational
end absint
