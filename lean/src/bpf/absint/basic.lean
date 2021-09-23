/-
Copyright (c) 2021 The UNSAT Group. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luke Nelson, Xi Wang
-/
import bpf.basic
import bpf.cfg
import data.domain.basic
import misc.bool
import .regs

namespace ai

section
parameters {CTRL REGS : Type} [regs_abstr REGS]
           [decidable_eq CTRL] {map : Type → Type} [generic_map CTRL map]
open unordered_map has_γ abstr_le abstr_top

abbreviation PGRM : Type := bpf.cfg.CFG (map (bpf.cfg.instr CTRL)) CTRL

/- Abstraction for memory. -/
abbreviation MEM := with_bot REGS

/- Abstract states are maps from CTRL → MEM. -/
abbreviation STATE := map MEM

/-- Interpret an abstract state. Use ⊥ for unmapped control points. -/
abbreviation interpret (s : STATE) (i : CTRL) : MEM :=
(lookup i s).get_or_else ⊥

structure constraint :=
(target  : CTRL)
(source  : CTRL)
(compute : MEM → MEM)

instance [has_repr CTRL] : has_repr constraint :=
⟨ λ c,
  "{ target := " ++ repr c.target ++ ", source := " ++ repr c.source ++ ", compute := XXX }" ⟩

abbreviation safety_predicate : Type :=
CTRL × (MEM → bool)

/-- Generate the constraints for a single BPF instruction. -/
def gen_one_constraint (current : CTRL) : bpf.cfg.instr CTRL → list constraint
| (bpf.cfg.instr.ALU64_X op dst src next) :=
  [{ target  := next,
     source  := current,
     compute := λ mem,
      (with_bot.lift_unary_transfer (regs_abstr.do_alu op dst src)).op mem }]
| (bpf.cfg.instr.ALU64_K op dst imm next) :=
  [{ target  := next,
     source  := current,
     compute := λ mem,
      (with_bot.lift_unary_transfer (regs_abstr.do_alu_imm op dst imm)).op mem }]
| (bpf.cfg.instr.JMP_X op dst src if_true if_false) :=
  [{ target  := if_true,
     source  := current,
     compute := λ mem,
       (with_bot.lift_arg_unary_inversion (regs_abstr.invert_jmp_tt op dst src)).inv mem },
   { target  := if_false,
     source  := current,
     compute := id }]
| (bpf.cfg.instr.JMP_K _ _ _ if_true if_false) :=
  [{ target  := if_true,
     source  := current,
     compute := id },
   { target  := if_false,
     source  := current,
     compute := id }]
| _ := []

/-- Generate the constraints for an entire program. -/
def gen_constraints (p : PGRM) : list constraint :=
{ target  := p.entry,
  source  := p.entry,
  compute := λ _, ⊤ } ::
(to_list p.code).bind (λ p, gen_one_constraint p.1 p.2)

/--
For a given ⟨pc, instr⟩ pair in the program, the `nth` members of `gen_one_constraint`
are all members of `gen_constraints` too.
-/
theorem gen_one_constraint_mem {p : PGRM} {pc : CTRL} {i : bpf.cfg.instr CTRL}
  (fetch : sigma.mk pc i ∈ to_list p.code)
  (n : ℕ)
  (h : n < (gen_one_constraint pc i).length . tactic.exact_dec_trivial) :
    (gen_one_constraint pc i).nth_le n h ∈ gen_constraints p :=
begin
  simp only [gen_constraints, list.mem_cons_iff, list.mem_bind],
  right,
  existsi [sigma.mk pc i, fetch],
  simp only [list.nth_le_mem]
end

/--
Generate the "check" whether the current state can step,
for example, DIV instructions are unsafe when the source register
can be zero.
-/
def gen_check : bpf.cfg.instr CTRL → MEM → bool
| (bpf.cfg.instr.ALU64_X bpf.ALU.DIV _ src _) :=
  (with_bot.lift_unary_test $ regs_abstr.test_reg_neq src 0).test
| (bpf.cfg.instr.ALU64_K bpf.ALU.DIV _ imm _) :=
  λ _, imm.nth ≠ 0
| (bpf.cfg.instr.ALU64_X bpf.ALU.END _ _ _) := λ _, ff
| (bpf.cfg.instr.ALU64_X bpf.ALU.MOD _ _ _) := λ _, ff
| (bpf.cfg.instr.ALU64_K bpf.ALU.END _ _ _) := λ _, ff
| (bpf.cfg.instr.ALU64_K bpf.ALU.MOD _ _ _) := λ _, ff
| _ := λ _, tt

/--
Generate the safety predicate for a single instruction.
Asserts that the next instruction is legal and any specific predicates
that must hold for the state to step (i.e., not error).
-/
def gen_one_safety (p : PGRM) (current : CTRL) : bpf.cfg.instr CTRL → MEM → bool
| i@(bpf.cfg.instr.ALU64_X _ dst src next) :=
  λ mem,
    (lookup next p.code).is_some ∧ gen_check i mem
| i@(bpf.cfg.instr.ALU64_K _ dst imm next) :=
  λ mem, (lookup next p.code).is_some ∧ gen_check i mem
| (bpf.cfg.instr.JMP_X _ _ _ if_true if_false) :=
  λ _, (lookup if_true p.code).is_some ∧ (lookup if_false p.code).is_some
| (bpf.cfg.instr.JMP_K _ _ _ if_true if_false) :=
  λ _, (lookup if_true p.code).is_some ∧ (lookup if_false p.code).is_some
| _ := λ _, tt

def gen_safety (p : PGRM) : list safety_predicate :=
(p.entry, λ _, (lookup p.entry p.code).is_some) ::
(to_list p.code).map (λ (i : Σ (_ : CTRL), bpf.cfg.instr CTRL), (i.1, gen_one_safety p i.1 i.2))

def secure (p : PGRM) (s : STATE) : Prop :=
∀ (pc : CTRL) (check : MEM → bool),
  (pc, check) ∈ (gen_safety p : list safety_predicate) →
  check (interpret s pc) = tt

/-
This instance is written in a weird way to avoid having the `eq.mpr` term from `simp`
take part in computation.
-/
instance (p : PGRM) (s : STATE) : decidable (secure p s) :=
by {
  cases @list.decidable_forall_mem (CTRL × (MEM → bool))
        (λ x, x.snd (interpret s x.fst) = tt) _ (gen_safety p),
  { left,
    simp only [secure, ← prod.forall', prod.mk.eta],
    exact h },
  { right,
    simp only [secure, ← prod.forall', prod.mk.eta],
    exact h } }

def constraint_holds (l : constraint) (s : STATE) : Prop :=
l.compute (interpret s l.source) ≤ interpret s l.target

instance (l : constraint) (s : STATE) : decidable (constraint_holds l s) :=
by { simp only [constraint_holds], apply_instance }

/--
An abstract state `s` approximates the behavior of P exactly when
F(s) ≤ s, where F is the transfer function on abstract states induced by the
`MEM → MEM` functions in the constraints.
-/
def approximates (p : PGRM) (s : STATE) : Prop :=
∀ ⦃c : constraint⦄,
  c ∈ (gen_constraints p : list constraint) →
  constraint_holds c s

instance (p : PGRM) (s : STATE) : decidable (approximates p s) :=
by apply list.decidable_forall_mem

/- Collecting semantics for BPF. Computes the set of reachable states for a program `p`. -/
def collect (p : PGRM) : set (bpf.cfg.state CTRL) :=
{ s | ∃ s₀, bpf.cfg.initial_state p s₀ ∧ bpf.cfg.star p s₀ s }

/--
Any initial BPF state is correctly approximated by the constraints.
-/
theorem init_approximation (p : PGRM) (s : STATE) (t₀ : bpf.cfg.state CTRL) :
  ∀ pc regs,
    bpf.cfg.state.running pc regs = t₀ →
    approximates p s →
    bpf.cfg.initial_state p t₀ →
    regs ∈ γ (interpret s pc) :=
begin
  intros _ _ _ approx init_t₀,
  subst_vars,
  specialize approx _,
  swap 2,
  { simp only [gen_constraints, list.mem_cons_iff],
    exact or.inl rfl },
  cases init_t₀,
  exact le_correct approx (top_correct _)
end

/--
Any state which approximates p respects the concretization function γ for the abstract
domain over states. In other words, `gen_constraints` is a sound transfer function
for the BPF semantics.
-/
theorem correct_approximation (p : PGRM) (s : STATE) :
  approximates p s →
  ∀ (pc : CTRL) (regs : bpf.reg → bpf.i64),
    bpf.cfg.state.running pc regs ∈ collect p →
    regs ∈ γ (interpret s pc) :=
begin
  intros approx pc regs reachable,
  simp only [collect] at reachable,
  rcases reachable with ⟨t₀, t_init, t_star⟩,
  generalize_hyp t_running : bpf.cfg.state.running pc regs = t at t_star,
  revert t_running regs pc,
  induction t_star with t' t'' head tail ih,
  { intros,
    apply init_approximation _ _ _ _ _ t_running approx t_init },
  { intros pc regs _,
    subst_vars,
    cases tail,
    case bpf.cfg.step.ALU64_X : pc' regs' op dst src v next fetch check doalu {
      specialize ih pc' regs' rfl,
      clear tail,
      subst doalu,
      rw [← option.mem_def, mem_lookup_iff] at fetch,
      specialize approx (gen_one_constraint_mem fetch 0),
      simp only [constraint_holds, gen_one_constraint, list.nth_le] at approx,
      apply le_correct approx,
      apply (with_bot.lift_unary_transfer (regs_abstr.do_alu op dst src)).correct ih },
    case bpf.cfg.step.ALU64_K : pc' regs' op dst imm v next fetch check doalu {
      specialize ih pc' regs' rfl,
      clear tail,
      subst doalu,
      rw [← option.mem_def, mem_lookup_iff] at fetch,
      specialize approx (gen_one_constraint_mem fetch 0),
      simp only [constraint_holds, gen_one_constraint, list.nth_le] at approx,
      apply le_correct approx,
      apply (with_bot.lift_unary_transfer (regs_abstr.do_alu_imm op dst imm)).correct ih },
    case bpf.cfg.step.JMP_X : pc' regs' op dst src v if_true if_false fetch dojmp {
      specialize ih pc' regs' rfl,
      clear tail,
      rw [← option.mem_def, mem_lookup_iff] at fetch,
      cases v,
      { -- Jump not taken,
        specialize approx (gen_one_constraint_mem fetch 1),
        apply le_correct approx,
        exact ih },
      { -- Jump taken
        specialize approx (gen_one_constraint_mem fetch 0),
        apply le_correct approx,
        apply (with_bot.lift_arg_unary_inversion (regs_abstr.invert_jmp_tt op dst src)).correct ih,
        symmetry,
        exact dojmp } },
    case bpf.cfg.step.JMP_K : pc' regs' op dst imm v if_true if_false fetch dojmp {
      specialize ih pc' regs' rfl,
      clear tail,
      rw [← option.mem_def, mem_lookup_iff] at fetch,
      cases v,
      { -- Jump not taken,
        specialize approx (gen_one_constraint_mem fetch 1),
        apply le_correct approx,
        exact ih },
      { -- Jump taken
        specialize approx (gen_one_constraint_mem fetch 0),
        apply le_correct approx,
        exact ih } } }
end

/-- A state is safe in a program if it can either take another step or has already exited. -/
def safeset (p : PGRM) : set (bpf.cfg.state CTRL) :=
{ s |
  (∃ s', bpf.cfg.step p s s') ∨
  (∃ r, s = bpf.cfg.state.exited r) }

/--
If the safety predicates hold then any reachable state always has an instruction
mapped at the PC. This is proved separately since it must be proven using induction
over the trace of states.
-/
theorem instruction_exists_of_secure (p : PGRM) (s : STATE) :
  secure p s →
  ∀ pc regs,
    bpf.cfg.state.running pc regs ∈ collect p →
    (lookup pc p.code).is_some :=
begin
  intros secure _ _ star,
  rcases star with ⟨t₀, init, star⟩,
  generalize_hyp t_running : bpf.cfg.state.running pc regs = t at star,
  induction star with t' t'' tail head ih generalizing init pc regs t_running,
  { subst t_running,
    cases init,
    specialize secure p.entry _ _,
    swap 2,
    { simp only [gen_safety, list.mem_cons_iff],
      exact or.inl rfl },
    exact secure },
  { subst t_running,
    specialize ih init,
    obtain ⟨pc', regs', backwards⟩ := bpf.cfg.running_backwards _ _ _ _ head,
    subst backwards,
    specialize ih pc' regs' rfl,
    specialize secure pc',
    simp only [option.is_some_iff_exists, ← option.mem_def, mem_lookup_iff] at ih,
    obtain ⟨instr, fetch⟩ := ih,
    simp only [gen_safety, list.mem_cons_iff, list.mem_map] at secure,
    specialize secure (gen_one_safety p pc' instr) _,
    { right,
      existsi [_, fetch],
      refl },
    rw [← mem_lookup_iff, option.mem_def] at fetch,
    cases head,
    case bpf.cfg.step.ALU64_X : pc' regs' op dst src v next fetch' check doalu {
      rw [fetch] at fetch',
      cases fetch',
      simp only [ai.gen_one_safety, band_eq_true_eq_eq_tt_and_eq_tt, bool.to_bool_and, bool.to_bool_coe] at secure,
      exact secure.1 },
    case bpf.cfg.step.ALU64_K : pc' regs' op dst imm v next fetch' check doalu {
      rw [fetch] at fetch',
      cases fetch',
      simp only [ai.gen_one_safety, band_eq_true_eq_eq_tt_and_eq_tt, bool.to_bool_and, bool.to_bool_coe] at secure,
      exact secure.1 },
    case bpf.cfg.step.JMP_X : pc' regs' op dst src _ if_true if_false fetch' {
      rw [fetch] at fetch',
      cases fetch',
      simp only [ai.gen_one_safety, band_eq_true_eq_eq_tt_and_eq_tt, bool.to_bool_and, bool.to_bool_coe] at secure,
      cases secure with secure₁ secure₂,
      cases head_c,
      { exact secure₂ },
      { exact secure₁ } },
    case bpf.cfg.step.JMP_K : pc' regs' op dst imm _ if_true if_false fetch' {
      rw [fetch] at fetch',
      cases fetch',
      simp only [ai.gen_one_safety, band_eq_true_eq_eq_tt_and_eq_tt, bool.to_bool_and, bool.to_bool_coe] at secure,
      cases secure with secure₁ secure₂,
      cases head_c,
      { exact secure₂ },
      { exact secure₁ } } }
end

/--
If a safety predicate holds for an instruction in the program and some abstract state,
and that abstract state models some concrete state, then the concrete state will be
able to take at least one step.
-/
theorem can_step_of_safety {p : PGRM} {s : STATE} {regs : bpf.reg → bpf.i64} {pc : CTRL} {i : bpf.cfg.instr CTRL} :
  gen_one_safety p pc i (interpret s pc) = tt →
  lookup pc p.code = some i →
  regs ∈ γ (interpret s pc) →
  ∃ (s' : bpf.cfg.state CTRL),
    bpf.cfg.step p (bpf.cfg.state.running pc regs) s' :=
begin
  intros check_tt fetch rel,
  cases i,
  case bpf.cfg.instr.ALU64_X : op dst src next {
    cases op,
    case bpf.ALU.DIV {
      simp only [ai.gen_one_safety, ai.gen_check, band_eq_true_eq_eq_tt_and_eq_tt, bool.to_bool_and, bool.to_bool_coe] at check_tt,
      existsi _,
      apply bpf.cfg.step.ALU64_X fetch _ rfl,
      apply (with_bot.lift_unary_test (regs_abstr.test_reg_neq src 0)).test_sound check_tt.2 rel },
    case bpf.ALU.MOD {
      simp only [ai.gen_one_safety, ai.gen_check, band_eq_true_eq_eq_tt_and_eq_tt, bool.to_bool_and, bool.to_bool_coe] at check_tt,
      cases check_tt.2 },
    case bpf.ALU.END {
      simp only [ai.gen_one_safety, ai.gen_check, band_eq_true_eq_eq_tt_and_eq_tt, bool.to_bool_and, bool.to_bool_coe] at check_tt,
      cases check_tt.2 },
    all_goals {
      existsi _,
      apply bpf.cfg.step.ALU64_X fetch rfl rfl } },
  case bpf.cfg.instr.ALU64_K : op dst imm next {
    cases op,
    case bpf.ALU.DIV {
      simp only [ai.gen_one_safety, ai.gen_check, band_eq_true_eq_eq_tt_and_eq_tt, bool.to_bool_and, bool.to_bool_coe] at check_tt,
      existsi _,
      exact bpf.cfg.step.ALU64_K fetch check_tt.2 rfl },
    case bpf.ALU.MOD {
      simp only [ai.gen_one_safety, ai.gen_check, band_eq_true_eq_eq_tt_and_eq_tt, bool.to_bool_and, bool.to_bool_coe] at check_tt,
      cases check_tt.2 },
    case bpf.ALU.END {
      simp only [ai.gen_one_safety, ai.gen_check, band_eq_true_eq_eq_tt_and_eq_tt, bool.to_bool_and, bool.to_bool_coe] at check_tt,
      cases check_tt.2 },
    all_goals { existsi _,
      apply bpf.cfg.step.ALU64_K fetch rfl rfl } },
  case bpf.cfg.instr.JMP_X {
    existsi _,
    apply bpf.cfg.step.JMP_X fetch rfl },
  case bpf.cfg.instr.JMP_K {
    existsi _,
    apply bpf.cfg.step.JMP_K fetch rfl },
  case bpf.cfg.instr.Exit {
    existsi _,
    apply bpf.cfg.step.Exit fetch },
end

/--
If an abstract state approximates the behavior of a program and the security checks
evaluate to `tt` for that state, then the set of reachable states of the program
is a subset of the set of safe states.
-/
theorem correctness (p : PGRM) (s : STATE) :
  approximates p s →
  secure p s →
  collect p ⊆ safeset p :=
begin
  intros ap_h se_h t t_reachable,
  simp only [collect] at t_reachable,
  rcases t_reachable with ⟨t₀, t_init, t_star⟩,
  cases t,
  case bpf.cfg.state.exited : res {
    right,
    existsi [res],
    refl },
  case bpf.cfg.state.running : pc regs {
    left,
    have fetch := instruction_exists_of_secure p s se_h pc regs ⟨_, ⟨t_init, t_star⟩⟩,
    rw [option.is_some_iff_exists] at fetch,
    rcases fetch with ⟨instr, fetch⟩,
    have gamma := correct_approximation p s ap_h pc regs ⟨_, ⟨t_init, t_star⟩⟩,
    apply can_step_of_safety _ fetch gamma,
    apply se_h,
    simp only [gen_safety],
    rw [list.mem_cons_iff],
    right,
    rw [list.mem_map],
    existsi (⟨pc, instr⟩ : Σ (_ : CTRL), bpf.cfg.instr CTRL),
    refine ⟨_, rfl⟩,
    simp only [← option.mem_def, mem_lookup_iff] at fetch,
    exact fetch }
end

/--
A rephrasing of `correctness` that demonstrates that it implies the definition
of program safety in `bpf.cfg`.
-/
theorem safe_program_of_correct_approximation (p : PGRM) (s : STATE) :
  approximates p s →
  secure p s →
  bpf.cfg.safe p :=
begin
  intros approx sec t h₁ t' h₂,
  exact correctness p s approx sec ⟨_, ⟨h₁, h₂⟩⟩
end

section solver

/-- The initial state is the empty map (i.e., maps everything to ⊥). -/
def initial_state : STATE :=
@unordered_map.empty CTRL _ (map MEM) _

/-- Refine an abstract state using a constraint and ⊔. -/
def refine (s : STATE) (c : constraint) : STATE :=
insert_with abstr_join.join c.target (c.compute (interpret s c.source)) s

/-- Refine a state using all constraints in a list. -/
def refine_all : STATE → list constraint → STATE
| s []        := s
| s (c :: cs) := refine_all (refine s c) cs

/-- Iterate refining a state with all contraints in the list `fuel` times. -/
def iterate (s : STATE) (l : list constraint) (fuel : ℕ) : STATE :=
nat.iterate (λ s, refine_all s l) fuel s

/-- Solve constraints by iterating `fuel` times on the initial state. -/
def solve (l : list constraint) (fuel : ℕ) : STATE :=
iterate initial_state l fuel

end solver
end -- section
end ai
