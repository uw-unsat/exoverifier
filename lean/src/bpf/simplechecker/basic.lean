/-
Copyright (c) 2021 The UNSAT Group. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luke Nelson, Xi Wang
-/
import ..basic
import ..cfg

namespace bpf
namespace simplechecker

section
parameters {α : Type} [decidable_eq α] {map : Type → Type} [generic_map α map]
open unordered_map

abbreviation program : Type := bpf.cfg.CFG (map (bpf.cfg.instr α)) α

private def check_from (p : program) : α → ℕ → bool
| pc 0       := ff
| pc (n + 1) :=
  match lookup pc p.code with
  | none := ff
  | some (bpf.cfg.instr.ALU64_X ALU.ADD _ _ next) := check_from next n
  | some bpf.cfg.instr.Exit := tt
  | _ := ff
  end

/- A very simple checker for BPF programs. -/
def check (p : program) (fuel : ℕ) : bool := check_from p p.entry fuel

private theorem check_from_sound {p : program} {pc : α} {fuel : ℕ} {s : bpf.cfg.state α} :
  (∃ r, s = bpf.cfg.state.running pc r) →
  check_from p pc fuel = tt →
  bpf.cfg.safe_from_state p s :=
begin
  revert s pc,
  induction fuel with fuel ih,
  { intros s pc h₁ h₂,
    cases h₂ },
  { intros s pc h₁ h₂,
    simp only [check_from] at h₂,
    cases h₃ : (lookup pc p.code),
    { rw [h₃] at h₂, cases h₂ },
    rw h₃ at h₂,
    cases val,
    case bpf.cfg.instr.ALU64_X : op dst src next {
      cases op; try {cases h₂},
      cases h₁ with regs h₁,
      subst h₁,
      apply cfg.safe_from_state_of_det_step,
      swap 2,
      { exact cfg.step.ALU64_X h₃ rfl rfl },
      { exact ih ⟨_, rfl⟩ h₂ },
      { exact cfg.step_alu64_x_det h₃ } },
    { cases h₂ },
    { cases h₂ },
    { cases h₂ },
    { cases h₂ },
    { cases h₁ with regs h₁,
      apply cfg.safe_from_state_of_det_step,
      apply cfg.safe_from_exited,
      { exact regs bpf.reg.R0 },
      { subst h₁,
        constructor,
        exact h₃ },
      { subst h₁,
        exact cfg.step_exit_det h₃ } } }
end

theorem check_sound {p : program} (fuel : ℕ) :
  check p fuel = tt →
  bpf.cfg.safe p :=
begin
  intros h₁ s h₂,
  cases h₂,
  apply check_from_sound,
  existsi _, refl,
  exact h₁
end

end
end simplechecker
end bpf
