/-
Copyright (c) 2021 The UNSAT Group. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luke Nelson, Xi Wang
-/
import .regs
import bpf.basic
import bpf.cfg
import data.domain.basic
import misc.bool

namespace absint

section
parameters {CTRL REGS : Type} [regs_abstr REGS]
           [decidable_eq CTRL] {map : Type → Type} [generic_map CTRL map]
open unordered_map has_γ abstr_le abstr_top

abbreviation PGRM : Type := bpf.cfg.CFG (map (bpf.cfg.instr CTRL)) CTRL

abbreviation STATE := with_bot REGS

/-- A SOLUTION maps each control point to a STATE or ⊥. -/
abbreviation SOLUTION := map STATE

/-- Interpret an abstract state. Use ⊥ for unmapped control points. -/
abbreviation interpret (s : SOLUTION) (i : CTRL) : STATE :=
(lookup i s).get_or_else ⊥

/-- A constraint computes a state for the "target" control point given a state for the "source" control point. -/
structure constraint :=
(target  : CTRL)
(source  : CTRL)
(compute : STATE → STATE)

instance [has_repr CTRL] : has_repr constraint :=
⟨ λ c,
  "{ target := " ++ repr c.target ++ ", source := " ++ repr c.source ++ ", compute := XXX }" ⟩

abbreviation safety_predicate : Type :=
CTRL × (STATE → bool)

/-- Generate the constraints for a single BPF instruction. -/
def gen_one_constraint (current : CTRL) : bpf.cfg.instr CTRL → list constraint
| (bpf.cfg.instr.ALU64_X op dst src next) :=
  [{ target  := next,
     source  := current,
     compute := (with_bot.lift_unary_relation (regs_abstr.do_alu op dst src)).op }]
| (bpf.cfg.instr.ALU64_K op dst imm next) :=
  [{ target  := next,
     source  := current,
     compute := (with_bot.lift_unary_relation (regs_abstr.do_alu_imm op dst imm)).op }]
| (bpf.cfg.instr.JMP_X op dst src if_true if_false) :=
  [{ target  := if_true,
     source  := current,
     compute := (with_bot.lift_arg_unary_inversion (regs_abstr.invert_jmp_tt op dst src)).inv },
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
| (bpf.cfg.instr.CALL func next) :=
  [{ target  := next,
     source  := current,
     compute := (with_bot.lift_unary_relation (regs_abstr.do_call func)).op }]
| _ := []

/-- Generate the constraints for an entire program. -/
def gen_constraints (p : PGRM) : list constraint :=
{ target  := p.entry,
  source  := p.entry,
  compute := λ _,
    (with_bot.lift_nullary_relation
      (regs_abstr.const (λ (_ : bpf.reg), bpf.value.uninitialized))).op } ::
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
Generate the safety predicate for a single instruction.
Asserts that the next instruction is legal and any specific predicates
that must hold for the state to step (i.e., not error).
-/
def gen_one_safety (p : PGRM) (current : CTRL) : bpf.cfg.instr CTRL → STATE → bool
| i@(bpf.cfg.instr.ALU64_X op dst src next) :=
  λ mem,
    (lookup next p.code).is_some ∧
    (with_bot.lift_unary_test (regs_abstr.do_alu_check op dst src)).test mem = tt
| i@(bpf.cfg.instr.ALU64_K op dst imm next) :=
  λ mem,
    (lookup next p.code).is_some ∧
    (with_bot.lift_unary_test (regs_abstr.do_alu_imm_check op dst imm)).test mem = tt
| (bpf.cfg.instr.JMP_X op dst src if_true if_false) :=
  λ mem,
    (lookup if_true p.code).is_some ∧
    (lookup if_false p.code).is_some ∧
    (with_bot.lift_unary_test (regs_abstr.do_jmp_check op dst src)).test mem = tt
| (bpf.cfg.instr.JMP_K op dst imm if_true if_false) :=
  λ mem,
    (lookup if_true p.code).is_some ∧
    (lookup if_false p.code).is_some ∧
    (with_bot.lift_unary_test (regs_abstr.do_jmp_imm_check op dst imm)).test mem = tt
| (bpf.cfg.instr.STX size dst src off next) :=
  λ _, (lookup next p.code).is_some ∧ false
| (bpf.cfg.instr.CALL func next) :=
  λ mem,
    (lookup next p.code).is_some ∧
    (with_bot.lift_unary_test (regs_abstr.do_call_check func)).test mem = tt
| bpf.cfg.instr.Exit :=
  (with_bot.lift_unary_test (regs_abstr.is_scalar bpf.reg.R0)).test

/--
Generate the safety conditions for a BPF program. It consists of a
special constraint that the entry point exists, and the constraints
generated for each individual instruction.
-/
def gen_safety (p : PGRM) : list safety_predicate :=
(p.entry, λ _, (lookup p.entry p.code).is_some) ::
(to_list p.code).map (λ (i : Σ (_ : CTRL), bpf.cfg.instr CTRL), (i.1, gen_one_safety p i.1 i.2))

def secure (p : PGRM) (s : SOLUTION) : Prop :=
∀ (pc : CTRL) (check : STATE → bool),
  (pc, check) ∈ (gen_safety p : list safety_predicate) →
  check (interpret s pc) = tt

/-
This instance is written in a weird way to avoid having the `eq.mpr` term from `simp`
take part in computation.
-/
instance (p : PGRM) (s : SOLUTION) : decidable (secure p s) :=
by {
  cases @list.decidable_forall_mem (CTRL × (STATE → bool))
        (λ x, x.snd (interpret s x.fst) = tt) _ (gen_safety p),
  { left,
    simp only [secure, ← prod.forall', prod.mk.eta],
    exact h },
  { right,
    simp only [secure, ← prod.forall', prod.mk.eta],
    exact h } }

def constraint_holds (l : constraint) (s : SOLUTION) : Prop :=
l.compute (interpret s l.source) ≤ interpret s l.target

instance (l : constraint) (s : SOLUTION) : decidable (constraint_holds l s) :=
by { simp only [constraint_holds], apply_instance }

/--
An abstract state `s` approximates the behavior of P exactly when
F(s) ≤ s, where F is the transfer function on abstract states induced by the
`MEM → MEM` functions in the constraints.
-/
def approximates (p : PGRM) (s : SOLUTION) : Prop :=
∀ ⦃c : constraint⦄,
  c ∈ (gen_constraints p : list constraint) →
  constraint_holds c s

instance (p : PGRM) (s : SOLUTION) : decidable (approximates p s) :=
by apply list.decidable_forall_mem

/- Collecting semantics for BPF. Computes the set of reachable states for a program `p`. -/
def collect (p : PGRM) (o : bpf.oracle) : set (bpf.cfg.state CTRL) :=
λ s, bpf.cfg.star p o (bpf.cfg.initial_state p o) s

/--
Any initial BPF state is correctly approximated by the constraints.
-/
theorem init_approximation (p : PGRM) (s : SOLUTION) :
  approximates p s →
  (λ _, bpf.value.uninitialized : bpf.reg → bpf.value) ∈ γ (interpret s p.entry) :=
begin
  intros approx,
  specialize approx _,
  swap 2,
  { simp only [gen_constraints, list.mem_cons_iff],
    exact or.inl rfl },
  apply le_correct approx _,
  apply (with_bot.lift_nullary_relation _).correct rfl
end

/--
Any state which approximates p respects the concretization function γ for the abstract
domain over states. In other words, `gen_constraints` is a sound transfer function
for the BPF semantics.
-/
theorem correct_approximation (p : PGRM) (o : bpf.oracle) (s : SOLUTION) :
  approximates p s →
  ∀ (s' : bpf.cfg.runstate CTRL),
    bpf.cfg.state.running s' ∈ collect p o →
    s'.regs ∈ γ (interpret s s'.pc) :=
begin
  intros approx _ reachable,
  simp only [collect] at reachable,
  generalize_hyp t_running : bpf.cfg.state.running s' = t at reachable,
  revert t_running s',
  induction reachable with t' t'' head tail ih,
  { intros,
    cases t_running,
    apply init_approximation _ _ approx },
  { intros s' _,
    subst_vars,
    cases tail,
    case bpf.cfg.step.ALU64_X : s₀ op dst src v next fetch check doalu {
      specialize ih s₀ rfl,
      clear tail,
      subst doalu,
      rw [← option.mem_def, mem_lookup_iff] at fetch,
      specialize approx (gen_one_constraint_mem fetch 0),
      simp only [constraint_holds, gen_one_constraint, list.nth_le] at approx,
      apply le_correct approx,
      apply (with_bot.lift_unary_relation (regs_abstr.do_alu op dst src)).correct ih rfl },
    case bpf.cfg.step.ALU64_K : s₀ op dst imm v next fetch check doalu {
      specialize ih s₀ rfl,
      clear tail,
      subst doalu,
      rw [← option.mem_def, mem_lookup_iff] at fetch,
      specialize approx (gen_one_constraint_mem fetch 0),
      simp only [constraint_holds, gen_one_constraint, list.nth_le] at approx,
      apply le_correct approx,
      apply (with_bot.lift_unary_relation (regs_abstr.do_alu_imm op dst imm)).correct ih rfl },
    case bpf.cfg.step.JMP_X : s₀ op dst src v if_true if_false fetch jmpcheck dojmp {
      specialize ih s₀ rfl,
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
    case bpf.cfg.step.JMP_K : s₀ op dst imm v if_true if_false fetch dojmp {
      specialize ih s₀ rfl,
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
        exact ih } },
    case bpf.cfg.step.CALL : s₀ func next fetch {
      specialize ih s₀ rfl,
      rw [← option.mem_def, mem_lookup_iff] at fetch,
      specialize approx (gen_one_constraint_mem fetch 0),
      apply le_correct approx,
      apply (with_bot.lift_unary_relation (regs_abstr.do_call func)).correct ih ⟨_, ⟨_, rfl⟩⟩ } }
end

/-- A state is safe in a program if it can either take another step or has already exited. -/
def safeset (p : PGRM) (o : bpf.oracle) : set (bpf.cfg.state CTRL) :=
{ s |
  (∃ s', bpf.cfg.step p o s s') ∨
  (∃ r, s = bpf.cfg.state.exited r) }

/--
If the safety predicates hold then any reachable state always has an instruction
mapped at the PC. This is proved separately since it must be proven using induction
over the trace of states.
-/
theorem instruction_exists_of_secure (p : PGRM) (o : bpf.oracle) (s : SOLUTION) :
  secure p s →
  ∀ (s' : bpf.cfg.runstate CTRL),
    bpf.cfg.state.running s' ∈ collect p o →
    (lookup s'.pc p.code).is_some :=
begin
  intros secure _ star,
  generalize_hyp t_running : bpf.cfg.state.running s' = t at star,
  simp only [collect] at star,
  induction star with t' t'' tail head ih generalizing s' t_running,
  { cases t_running,
    specialize secure p.entry _ _,
    swap 2,
    { simp only [gen_safety, list.mem_cons_iff],
      exact or.inl rfl },
    exact secure },
  { subst t_running,
    obtain ⟨s₀, backwards⟩ := bpf.cfg.running_backwards _ _ _ _ head,
    subst backwards,
    specialize ih s₀ rfl,
    specialize secure s₀.pc,
    simp only [option.is_some_iff_exists, ← option.mem_def, mem_lookup_iff] at ih,
    obtain ⟨instr, fetch⟩ := ih,
    simp only [gen_safety, list.mem_cons_iff, list.mem_map] at secure,
    specialize secure (gen_one_safety p s₀.pc instr) _,
    { right,
      existsi [_, fetch],
      refl },
    rw [← mem_lookup_iff, option.mem_def] at fetch,
    cases head,
    case bpf.cfg.step.ALU64_X : _ op dst src v next fetch' check doalu {
      rw [fetch] at fetch',
      cases fetch',
      simp only [absint.gen_one_safety, band_eq_true_eq_eq_tt_and_eq_tt, bool.to_bool_and, bool.to_bool_coe] at secure,
      exact secure.1 },
    case bpf.cfg.step.ALU64_K : _ op dst imm v next fetch' check doalu {
      rw [fetch] at fetch',
      cases fetch',
      simp only [absint.gen_one_safety, band_eq_true_eq_eq_tt_and_eq_tt, bool.to_bool_and, bool.to_bool_coe] at secure,
      exact secure.1 },
    case bpf.cfg.step.JMP_X : _ op dst src _ if_true if_false fetch' {
      rw [fetch] at fetch',
      cases fetch',
      simp only [absint.gen_one_safety, band_eq_true_eq_eq_tt_and_eq_tt, bool.to_bool_and, bool.to_bool_coe] at secure,
      rcases secure with ⟨secure₁, secure₂, -⟩,
      cases head_c,
      { exact secure₂ },
      { exact secure₁ } },
    case bpf.cfg.step.JMP_K : _ op dst imm _ if_true if_false fetch' {
      rw [fetch] at fetch',
      cases fetch',
      simp only [absint.gen_one_safety, band_eq_true_eq_eq_tt_and_eq_tt, bool.to_bool_and, bool.to_bool_coe] at secure,
      rcases secure with ⟨secure₁, secure₂, -⟩,
      cases head_c,
      { exact secure₂ },
      { exact secure₁ } },
    case bpf.cfg.step.CALL : _ _ next fetch' {
      rw [fetch] at fetch',
      cases fetch',
      simp only [absint.gen_one_safety, band_eq_true_eq_eq_tt_and_eq_tt, bool.to_bool_and, bool.to_bool_coe] at secure,
      rcases secure with ⟨secure₁, -⟩,
      exact secure₁ } }
end

/--
If a safety predicate holds for an instruction in the program and some abstract state,
and that abstract state models some concrete state, then the concrete state will be
able to take at least one step.
-/
theorem can_step_of_safety {p : PGRM} {o : bpf.oracle} {s : SOLUTION} {c : bpf.cfg.runstate CTRL} {i : bpf.cfg.instr CTRL} :
  gen_one_safety p c.pc i (interpret s c.pc) = tt →
  lookup c.pc p.code = some i →
  c.regs ∈ γ (interpret s c.pc) →
  ∃ (s' : bpf.cfg.state CTRL),
    bpf.cfg.step p o (bpf.cfg.state.running c) s' :=
begin
  intros check_tt fetch rel,
  cases i,
  case bpf.cfg.instr.ALU64_X : op dst src next {
    simp only [absint.gen_one_safety, band_eq_true_eq_eq_tt_and_eq_tt, bool.to_bool_and, bool.to_bool_coe] at check_tt,
    existsi _,
    apply bpf.cfg.step.ALU64_X _ fetch _ rfl,
    cases check_tt with _ check_tt,
    exact (with_bot.lift_unary_test (regs_abstr.do_alu_check _ dst src)).test_sound check_tt rel },
  case bpf.cfg.instr.ALU64_K : op dst imm next {
    simp only [absint.gen_one_safety, band_eq_true_eq_eq_tt_and_eq_tt, bool.to_bool_and, bool.to_bool_coe] at check_tt,
    existsi _,
    apply bpf.cfg.step.ALU64_K _ fetch _ rfl,
    cases check_tt with _ check_tt,
    exact (with_bot.lift_unary_test (regs_abstr.do_alu_imm_check _ dst imm)).test_sound check_tt rel },
  case bpf.cfg.instr.JMP_X : op dst src if_true if_false {
    simp only [absint.gen_one_safety, band_eq_true_eq_eq_tt_and_eq_tt, bool.to_bool_and, bool.to_bool_coe] at check_tt,
    rcases check_tt with ⟨-, -, check_tt⟩,
    existsi _,
    apply bpf.cfg.step.JMP_X _ fetch _ rfl,
    exact (with_bot.lift_unary_test (regs_abstr.do_jmp_check _ dst src)).test_sound check_tt rel },
  case bpf.cfg.instr.JMP_K : op dst imm if_true if_false {
    simp only [absint.gen_one_safety, band_eq_true_eq_eq_tt_and_eq_tt, bool.to_bool_and, bool.to_bool_coe] at check_tt,
    rcases check_tt with ⟨-, -, check_tt⟩,
    existsi _,
    apply bpf.cfg.step.JMP_K _ fetch _ rfl,
    exact (with_bot.lift_unary_test (regs_abstr.do_jmp_imm_check _ dst _)).test_sound check_tt rel },
  case bpf.cfg.instr.STX {
    simp only [gen_one_safety, to_bool_false_eq_ff, and_false] at check_tt,
    cases check_tt },
  case bpf.cfg.instr.CALL {
    simp only [absint.gen_one_safety, band_eq_true_eq_eq_tt_and_eq_tt, bool.to_bool_and, bool.to_bool_coe] at check_tt,
    rcases check_tt with ⟨-, check_tt⟩,
    existsi _,
    apply bpf.cfg.step.CALL _ fetch _,
    apply (with_bot.lift_unary_test (regs_abstr.do_call_check _)).test_sound check_tt rel },
  case bpf.cfg.instr.Exit {
    simp only [absint.gen_one_safety, band_eq_true_eq_eq_tt_and_eq_tt, bool.to_bool_and, bool.to_bool_coe] at check_tt,
    have h_ok := (with_bot.lift_unary_test (regs_abstr.is_scalar _)).test_sound check_tt rel,
    simp only [to_bool_iff] at h_ok,
    cases h_ok with retval retval_h,
    existsi _,
    apply bpf.cfg.step.Exit _ fetch retval_h },
end

/--
If an abstract state approximates the behavior of a program and the security checks
evaluate to `tt` for that state, then the set of reachable states of the program
is a subset of the set of safe states.
-/
theorem correctness (p : PGRM) (o : bpf.oracle) (s : SOLUTION) :
  approximates p s →
  secure p s →
  collect p o ⊆ safeset p o :=
begin
  intros ap_h se_h t t_reachable,
  simp only [collect] at t_reachable,
  cases t,
  case bpf.cfg.state.exited : res {
    right,
    existsi [res],
    refl },
  case bpf.cfg.state.running : c {
    left,
    have fetch := instruction_exists_of_secure p o s se_h c t_reachable,
    rw [option.is_some_iff_exists] at fetch,
    rcases fetch with ⟨instr, fetch⟩,
    have gamma := correct_approximation p o s ap_h c t_reachable,
    apply can_step_of_safety _ fetch gamma,
    apply se_h,
    simp only [gen_safety],
    rw [list.mem_cons_iff],
    right,
    rw [list.mem_map],
    existsi (⟨c.pc, instr⟩ : Σ (_ : CTRL), bpf.cfg.instr CTRL),
    refine ⟨_, rfl⟩,
    simp only [← option.mem_def, mem_lookup_iff] at fetch,
    exact fetch }
end

/--
A rephrasing of `correctness` that demonstrates that it implies the definition
of program safety in `bpf.cfg`.
-/
theorem safe_program_of_correct_approximation (p : PGRM) (s : SOLUTION) :
  approximates p s →
  secure p s →
  bpf.cfg.safe p :=
begin
  intros approx sec o t h₁,
  exact correctness p o s approx sec h₁
end

namespace solver

/-- The initial state is the empty map (i.e., maps everything to ⊥). -/
private def initial_state : SOLUTION :=
@unordered_map.empty CTRL _ SOLUTION _

/-- Refine an abstract state using a constraint and ⊔. -/
private def refine (s : SOLUTION) (c : constraint) : SOLUTION :=
insert_with abstr_join.join c.target (c.compute (interpret s c.source)) s

/-- Refine a state using all constraints in a list. -/
private def refine_all : SOLUTION → list constraint → SOLUTION
| s []        := s
| s (c :: cs) := refine_all (refine s c) cs

/--
Iterate refining a state with all contraints in the list `fuel` times.
Stop early if a state is found which satisfies the constraints.
-/
private def iterate (l : list constraint) : SOLUTION → ℕ → SOLUTION
| s 0       := s
| s (n + 1) :=
  if ∀ c, c ∈ l → constraint_holds c s
  then s
  else iterate (refine_all s l) n

/-- Solve constraints by iterating `fuel` times on the initial state. -/
def solve (l : list constraint) (fuel : ℕ) : SOLUTION :=
iterate l initial_state fuel

end solver
end -- section
end absint
