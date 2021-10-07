/-
Copyright (c) 2021 The UNSAT Group. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luke Nelson, Xi Wang
-/
import .basic

namespace bpf
namespace cfg
namespace se

open bpf bpf.cfg factory.monad factory smt.extract_factory smt.neg_factory smt.add_factory
     smt.and_factory smt.const_factory smt.eq_factory smt.implies_factory smt.redor_factory
     smt.not_factory smt.or_factory smt.var_factory smt.udiv_factory smt.xor_factory
     smt.sub_factory smt.ult_factory smt.ule_factory smt.slt_factory smt.sle_factory
     smt.mul_factory smt.shl_factory smt.lshr_factory smt.ashr_factory smt.ite_factory
open unordered_map

section proof

universes u
variables
  {χ : Type*} {η β γ : Type u}
  [unordered_map η (bpf.cfg.instr η) χ] [decidable_eq η]
  [smt.factory β γ] [smt.extract_factory β γ] [smt.neg_factory β γ] [smt.add_factory β γ]
  [smt.and_factory β γ] [smt.const_factory β γ] [smt.eq_factory β γ] [smt.implies_factory β γ]
  [smt.redor_factory β γ] [smt.not_factory β γ] [smt.or_factory β γ] [smt.var_factory β γ]
  [smt.udiv_factory β γ] [smt.xor_factory β γ] [smt.sub_factory β γ] [smt.ult_factory β γ]
  [smt.mul_factory β γ] [smt.shl_factory β γ] [smt.lshr_factory β γ] [smt.ite_factory β γ]

@[reducible]
def bv_sig {n : ℕ} (f : fin n → bool) : Σ n, fin n → bool := ⟨n, f⟩

@[reducible]
def bv1 (b : bool) := bv_sig (λ (_ : fin 1), b)

theorem bv1_eq_iff (b₁ b₂ : bool) :
  (bv1 b₁ = bv1 b₂) ↔ b₁ = b₂ :=
begin
  simp only [bv1, bv_sig],
  split; intros h,
  { simp only [true_and, eq_self_iff_true, heq_iff_eq] at h,
    replace h := congr_fun h 0,
    tauto },
  { subst h,
    tauto }
end

/-- `concretizes` relates symbolic states to concrete state in some SMT factory. -/
@[mk_iff]
structure concretizes (g : γ) (abs : symstate β η) (asserts assumes : bool) (regs : reg → value) : Prop :=
(asserts_ok : sat g abs.assertions (bv1 asserts))
(assumes_ok : sat g abs.assumptions (bv1 assumes))
(regs_ok    : ∀ (r : reg), sat g (abs.regs r) (regs r))

namespace concretizes

theorem of_le {abs : symstate β η} {asserts assumes : bool} {regs : reg → value} {g₁ g₂ : γ} :
  g₁ ≤ g₂ →
  concretizes g₁ abs asserts assumes regs →
  concretizes g₂ abs asserts assumes regs :=
begin
  intros l c,
  cases c,
  constructor,
  { exact sat_of_le l c_asserts_ok },
  { exact sat_of_le l c_assumes_ok },
  { intros r,
    apply sat_of_le l,
    tauto }
end

end concretizes

theorem die_increasing : increasing (die : state γ β) := by apply le_mk_const

theorem assume_increasing (c : β) (s : symstate β η) : increasing (assume_ c s : state γ (symstate β η)) :=
begin
  apply increasing_bind,
  apply le_mk_and,
  apply increasing_pure
end

theorem assume_assertions_eq {s : symstate β η} {g : γ} {c : β} :
  ((assume_ c s).run g).fst.assertions = s.assertions :=
begin
  simp only [assume_, state_t.run_bind], refl,
end

theorem assert_increasing (c : β) (s : symstate β η) : increasing (assert c s : state γ (symstate β η)) :=
begin
  apply increasing_bind,
  apply le_mk_implies,
  intros, apply increasing_bind,
  apply le_mk_and,
  intros apply increasing_bind,
  apply increasing_pure
end

theorem assert_assumptions_eq {s : symstate β η} {g : γ} {c : β} :
  ((assert c s).run g).fst.assumptions = s.assumptions :=
by simpa only [assert, state_t.run_bind]

theorem assert_spec {s s' : symstate β η} {g g' : γ} {c : β} {as asserts assumes : bool} {regs : reg → value} :
  concretizes g s asserts assumes regs →
  sat g c (bv1 as) →
  (assert c s).run g = (s', g') →
  concretizes g' s' (asserts && (bimplies assumes as)) assumes regs :=
begin
  intros pre sat mk,
  have inc : g ≤ _ := assert_increasing c s,
  rw [mk] at inc,
  simp only [assert, state_t.run_bind] at mk,
  cases mk, clear mk,
  apply concretizes.mk,
  { refine sat_mk_and (by rw [prod.mk.eta]) _ _,
    { exact sat_of_le (by apply le_mk_implies) pre.asserts_ok },
    { exact sat_mk_implies (by rw [prod.mk.eta]) pre.assumes_ok sat } },
  { exact sat_of_le inc pre.assumes_ok },
  { exact λ r, sat_of_le inc (pre.regs_ok r) }
end

theorem assume_spec {s s' : symstate β η} {g g' : γ} {c : β} {as asserts assumes : bool} {regs : reg → value} :
  concretizes g s asserts assumes regs →
  sat g c (bv1 as) →
  (assume_ c s).run g = (s', g') →
  concretizes g' s' asserts (as && assumes) regs :=
begin
  intros pre sat mk,
  have inc : g ≤ _ := assume_increasing c s,
  rw [mk] at inc,
  simp only [assume_, state_t.run_bind] at mk,
  cases mk, clear mk,
  apply concretizes.mk,
  { exact sat_of_le inc pre.asserts_ok },
  { exact sat_mk_and (by rw [prod.mk.eta]) sat pre.assumes_ok },
  { exact λ r, sat_of_le inc (pre.regs_ok r) }
end

/-- The actual symbolic evaluation routine is continuation-based, so the
    correctness of one of these functions inductively depends on the correctness
    of the continuation. -/
def se_correct (cfg : CFG χ η) (p : set (symstate β η)) (k : symstate β η → state γ β) : Prop :=
∀ ⦃g g' : γ⦄ ⦃c : β⦄ ⦃abs : symstate β η⦄ ⦃asserts assumes : bool⦄ ⦃regs : reg → value⦄,
  -- If the abstract state is one we care about, and
  abs ∈ p →
  -- the abstract state concretizes to a legitimate state, and
  concretizes g abs asserts assumes regs →
  -- we run the the continuation to get a vc expression and a final factory,
  (k abs).run g = (c, g') →

  -- Then there exists an interpretation of the verification condition s.t.
  ∃ (vc : bool),
    sat g' c (bv1 vc) ∧
    -- If the current assumptions are true, and the VC is true, then
    (assumes = tt → vc = tt →
      -- The asserts at this point hold, and
      asserts = tt ∧
      -- Then the concrete state is safe from this point onwards.
      bpf.cfg.safe_from_state cfg (state.running abs.current regs))

namespace se_correct

theorem weaken {cfg : CFG χ η} {p p' : set (symstate β η)} {k : symstate β η → state γ β} :
  se_correct cfg p k →
  p' ⊆ p →
  se_correct cfg p' k :=
λ h l _ _ _ _ _ _ _ m, h $ l m

end se_correct

theorem step_jmp64_x_increasing {cfg : CFG χ η} {k : symstate β η → state γ β} (ih : ∀ s, increasing (k s)) :
  ∀ op dst src if_true if_false s,
    increasing (step_jmp64_x cfg k op dst src if_true if_false s)
| op dst src if_true if_false s := by {
  apply increasing_bind; intros,
  apply symvalue.doJMP_check_increasing,
  apply increasing_bind; intros,
  apply assert_increasing,
  apply increasing_bind; intros,
  apply symvalue.doJMP_increasing,
  apply increasing_bind; intros,
  apply le_mk_not,
  apply increasing_bind; intros,
  apply assume_increasing,
  apply increasing_bind; intros,
  apply ih,
  apply increasing_bind; intros,
  apply assume_increasing,
  apply increasing_bind; intros,
  apply ih,
  apply le_mk_and }

theorem step_jmp64_k_increasing {cfg : CFG χ η} {k : symstate β η → state γ β} (ih : ∀ s, increasing (k s)) :
  ∀ op dst imm if_true if_false s,
    increasing (step_jmp64_k cfg k op dst imm if_true if_false s)
| op dst imm if_true if_false s := by {
  apply increasing_bind; intros,
  apply symvalue.le_mk_scalar,
  apply increasing_bind; intros,
  apply symvalue.doJMP_check_increasing,
  apply increasing_bind; intros,
  apply assert_increasing,
  apply increasing_bind; intros,
  apply symvalue.doJMP_increasing,
  apply increasing_bind; intros,
  apply le_mk_not,
  apply increasing_bind; intros,
  apply assume_increasing,
  apply increasing_bind; intros,
  apply ih,
  apply increasing_bind; intros,
  apply assume_increasing,
  apply increasing_bind; intros,
  apply ih,
  apply le_mk_and }

theorem step_alu64_x_increasing {cfg : CFG χ η} {k : symstate β η → state γ β} (k_mon : ∀ s, increasing (k s)) :
  ∀ op dst src next s,
    increasing (step_alu64_x cfg k op dst src next s) :=
begin
  intros op dst src next s,
  apply increasing_bind, intros,
  apply symvalue.doALU_check_increasing, intros,
  apply increasing_bind,
  apply assert_increasing, intros,
  apply increasing_bind,
  apply symvalue.doALU_increasing, intros,
  apply k_mon
end

theorem step_alu64_k_increasing {cfg : CFG χ η} {k : symstate β η → state γ β} (k_mon : ∀ s, increasing (k s)) :
  ∀ op dst imm next s,
    increasing (step_alu64_k cfg k op dst imm next s) :=
begin
  intros op dst imm next s,
  apply increasing_bind,
  apply symvalue.le_mk_scalar,
  intro c,
  apply increasing_bind,
  apply symvalue.doALU_check_increasing,
  intro c,
  apply increasing_bind,
  apply assert_increasing,
  intro c,
  apply increasing_bind,
  apply symvalue.doALU_increasing,
  intro c,
  apply k_mon
end

theorem step_symeval_increasing
  {cfg : CFG χ η} {k : symstate β η → state γ β} {ih : ∀ s, increasing (k s)} ⦃s : symstate β η⦄ :
    increasing (step_symeval cfg k s) :=
begin
  dsimp only [step_symeval],
  intros g,
  cases instr_i : lookup s.current cfg.code,
  case option.none {
    apply die_increasing },
  case option.some : val {
    cases val; try{apply h},
    case instr.ALU64_X : op dst src next {
      apply step_alu64_x_increasing ih },
    case instr.ALU64_K : op dst imm next {
      apply step_alu64_k_increasing ih },
    case instr.JMP_X : op r₁ r₂ if_true if_false {
      apply step_jmp64_x_increasing ih },
    case instr.JMP_K : op r₁ imm if_true if_false {
      apply step_jmp64_k_increasing ih },
    case instr.STX : op dst src off next {
      apply die_increasing },
    case instr.Exit { refl } }
end

theorem symeval_increasing {cfg : CFG χ η} {fuel : ℕ} :
  ∀ ⦃s : symstate β η⦄, increasing (symeval cfg fuel s : state γ β) :=
begin
  induction fuel; intros s,
  { apply le_mk_not },
  { rw [symeval],
    apply step_symeval_increasing,
    assumption }
end

theorem initial_regs_increasing : ∀ {n : ℕ} {r : erased (vector i64 n)},
  increasing (se.initial_regs r : state γ (vector β n))
| 0       := λ _, by apply increasing_pure
| (n + 1) := by {
  intro regs,
  simp only [se.initial_regs],
  apply increasing_bind,
  { apply le_mk_var },
  intro c,
  apply increasing_bind,
  { apply @initial_regs_increasing },
  intro c',
  apply increasing_pure }

theorem initial_regs_spec : ∀ {n : ℕ} {regs : erased (vector i64 n)} {regs' : vector β n} {g g' : γ},
  (se.initial_regs regs).run g = (regs', g') →
  ∀ {r : fin n},
    sat g' (regs'.nth r) (sigma.mk 64 (regs.out.nth r) : Σ n, fin n → bool)
| 0       _    _     _ _  _   := fin.elim0
| (n + 1) regs regs' g g' mk' := λ r, by {
  simp only [se.initial_regs, state_t.run_bind] at mk',
  cases mk', clear mk',
  refine fin.cases _ _ r,
  { simp only [vector.nth_zero, vector.cons_head],
    refine sat_of_le (by apply initial_regs_increasing) _,
    rw [← erased.out_mk (regs.out.head)],
    apply sat_mk_var,
    simp only [vector.nth_zero, erased.map, erased.bind_eq_out, prod.mk.eta] },
  { simp only [vector.nth_cons_succ],
    intros i,
    simp only [erased.map, erased.bind_eq_out, erased.out_mk, erased.mk_out, function.comp],
    rw [← vector.cons_head_tail regs.out, vector.tail_cons, vector.head_cons, vector.nth_cons_succ],
    rw [← erased.out_mk (regs.out.tail)],
    apply initial_regs_spec,
    simp only [erased.mk_out, erased.out_mk, prod.mk.eta] } }

theorem initial_state_increasing (cfg : CFG χ η) (regs' : erased (vector i64 bpf.nregs)) :
  increasing (initial_symstate cfg regs' : state γ (symstate β η)) :=
begin
  simp only [initial_symstate],
  apply increasing_bind,
  apply le_mk_const,
  intro c, apply increasing_bind,
  apply initial_regs_increasing,
  intro c, apply increasing_pure
end

theorem initial_symstate_spec
  (g : γ) {g' : γ} {s : symstate β η} (cfg : CFG χ η) (regs : erased (vector i64 bpf.nregs)) :
    (initial_symstate cfg regs).run g = (s, g') →
    concretizes g' s tt tt (bpf.reg.of_vector regs.out) :=
begin
  intros mk,
  simp only [initial_symstate, state_t.run_bind] at mk,
  injection mk with h₁ h₂, subst h₁, subst h₂, clear mk,
  apply concretizes.mk; simp only,
  { exact sat_of_le (by apply initial_regs_increasing) (sat_mk_true (by rw [prod.mk.eta])) },
  { exact sat_of_le (by apply initial_regs_increasing) (sat_mk_true (by rw [prod.mk.eta])) },
  { simp only [reg.of_vector],
    intros r,
    apply initial_regs_spec,
    rw [prod.mk.eta] }
end

theorem initial_symstate_current {g : γ} {cfg : CFG χ η} {regs : erased (vector i64 bpf.nregs)} :
  ((initial_symstate cfg regs : state γ (symstate β η)).run g).1.current = (CFG.entry cfg) :=
begin
  simp only [initial_symstate, state_t.run_bind],
  refl
end

/-- "die" is a correct symbolic evaluator (that rejects everything). -/
theorem die_correct {cfg : CFG χ η} : se_correct cfg ⊤ (λ (_ : symstate β η), (die : state γ β)) :=
begin
  rintros _ _ _ _ _ _ _ ⟨⟩ assumes_sat die_mk,
  existsi ff,
  split,
  { simp only [die, state_t.run_map, state_t.run_get] at die_mk,
    apply sat_mk_false die_mk },
  { tauto }
end

theorem infeasible_correct {cfg : CFG χ η} : se_correct cfg ⊤ (infeasible : symstate β η → state γ β) :=
begin
  rintros _ _ _ _ _ _ _ ⟨⟩ pre die_mk,
  existsi (!assumes),
  split,
  { simp only [infeasible] at die_mk,
    exact sat_mk_not die_mk pre.assumes_ok },
  { intros f₁ f₂,
    exfalso,
    rw [f₁] at f₂,
    cases f₂ }
end

open concretizes

theorem doJMP_spec {g g' : γ} {dst src cond : β} {dst_c src_c : i64} {op : bpf.JMP} :
  (doJMP op dst src).run g = (cond, g') →
  sat g dst (bv_sig dst_c) →
  sat g src (bv_sig src_c) →
  sat g' cond (bv1 (bpf.JMP.doJMP op dst_c src_c)) :=
begin
  intros mk sat₁ sat₂,
  cases op; simp only [doJMP, state_t.run_bind] at mk,
  case JEQ {
    exact sat_mk_eq mk sat₁ sat₂ },
  case JNE {
    convert (sat_mk_not mk (sat_mk_eq (by rw [prod.mk.eta]) sat₁ sat₂)),
    simp only [bv1, bv.not, bpf.JMP.doJMP],
    congr, funext i,
    simp only [bool.to_bool_not] },
  case JSET {
    convert (sat_mk_redor mk _),
    { rw [bv.any_eq_to_bool_nonzero], refl },
    exact sat_mk_and (by rw [prod.mk.eta]) sat₁ sat₂ },
  case JLT {
    exact sat_mk_ult mk sat₁ sat₂ },
  case JGT {
    exact sat_mk_ult mk sat₂ sat₁ },
  case JLE {
    exact sat_mk_ule mk sat₁ sat₂ },
  case JGE {
    exact sat_mk_ule mk sat₂ sat₁ },
  case JSLT {
    exact sat_mk_slt mk sat₁ sat₂ },
  case JSGT {
    exact sat_mk_slt mk sat₂ sat₁ },
  case JSLE {
    exact sat_mk_sle mk sat₁ sat₂ },
  case JSGE {
    exact sat_mk_sle mk sat₂ sat₁ },
  -- all_goals {
  --   simp only [doJMP] at mk,
  --   rw [prod.eq_iff_fst_eq_snd_eq] at mk, simp only at mk, cases mk with m₁ m₂,
  --   subst m₁, subst m₂,
  --   simp only [bv1, bv_sig],
  --   rw [denote64_sound sat₁, denote64_sound sat₂],
  --   rw [← vector.nth_of_fn_ext (λ (x : fin 1), bpf.JMP.doJMP _ dst_c src_c)],
  --   apply sat_mk_var,
  --   simp only [prod.mk.eta, vector.of_fn_nth] }
end

/--
  step_jmp64_x is a correct symbolic evaluator when the current instruction is JMP_X and
  the continuation is correct for any state.
-/
theorem step_jmp64_x_correct
  {cfg : CFG χ η} {k : symstate β η → state γ β}
  (k_inc : ∀ s, increasing (k s)) (ih : se_correct cfg ⊤ k)
  {op : JMP} {dst src : reg} {if_true if_false : η} :
    se_correct cfg (λ s, lookup s.current cfg.code = some (instr.JMP_X op dst src if_true if_false))
               (step_jmp64_x cfg k op dst src if_true if_false) :=
begin
  intros _ _ vc _ _ _ _ fetch_i pre mk,
  simp only [step_jmp64_x, state_t.run_bind] at mk,
  cases f₁ : (doJMP op (abs.regs dst) (abs.regs src)).run g with eq g₁,
  cases f₂ : (mk_not eq).run g₁ with neq g₂,
  cases f₃ : (assume_ eq abs).run g₂ with truestate g₃,
  cases f₄ : (k {current := if_true, ..truestate}).run g₃ with true_condition g₄,
  cases f₅ : (assume_ neq abs).run g₄ with falsestate g₅,
  cases f₆ : (k {current := if_false, ..falsestate}).run g₅ with false_condition g₆,
  cases f₇ : (mk_and true_condition false_condition).run g₆ with result g₆,
  simp only [has_bind.bind, id_bind] at mk,
  rw [f₁, f₂, f₃, f₄, f₅, f₆, f₇] at mk,
  cases mk, clear mk,

  have l₁ : g ≤ g₁,
  { obtain ⟨-, r⟩ := prod.eq_iff_fst_eq_snd_eq.1 f₁, simp only at r, rw [← r],
    apply doJMP_increasing },
  have l₂ : g₁ ≤ g₂,
  { obtain ⟨-, r⟩ := prod.eq_iff_fst_eq_snd_eq.1 f₂, simp only at r, rw [← r],
    apply le_mk_not },
  have l₃ : g₂ ≤ g₃,
  { obtain ⟨-, r⟩ := prod.eq_iff_fst_eq_snd_eq.1 f₃, simp only at r, rw [← r],
    apply assume_increasing },
  have l₄ : g₃ ≤ g₄,
  { obtain ⟨-, r⟩ := prod.eq_iff_fst_eq_snd_eq.1 f₄, simp only at r, rw [← r],
    apply k_inc },
  have l₅ : g₄ ≤ g₅,
  { obtain ⟨-, r⟩ := prod.eq_iff_fst_eq_snd_eq.1 f₅, simp only at r, rw [← r],
    apply assume_increasing },
  have l₆ : g₅ ≤ g₆,
  { obtain ⟨-, r⟩ := prod.eq_iff_fst_eq_snd_eq.1 f₆, simp only at r, rw [← r],
    apply k_inc },
  have l₇ : g₆ ≤ g',
  { obtain ⟨-, r⟩ := prod.eq_iff_fst_eq_snd_eq.1 f₇, simp only at r, rw [← r],
    apply le_mk_and },

  rename ih → ih₁,
  have ih₂ := ih₁,
  specialize @ih₁ g₃ g₄ true_condition {current := if_true, ..truestate} asserts ((bpf.JMP.doJMP op (regs dst) (regs src)) && assumes) regs true.intro _ f₄,
  { convert (assume_spec _ _ f₃) using 0,
    { simp only [concretizes_iff] },
    { refine of_le (le_trans l₁ l₂) pre },
    { obtain ⟨-, r⟩ := prod.eq_iff_fst_eq_snd_eq.1 f₂, simp only at r, rw [← r], clear r,
      obtain ⟨l, r⟩ := prod.eq_iff_fst_eq_snd_eq.1 f₁, simp only at l r, rw [← l, ← r], clear l, clear r,
      refine sat_of_le le_mk_not _,
      exact doJMP_spec (by rw [prod.mk.eta]) (pre.regs_ok dst) (pre.regs_ok src) } },
  specialize @ih₂ g₅ g₆ false_condition {current := if_false, ..falsestate} asserts (!(bpf.JMP.doJMP op (regs dst) (regs src)) && assumes) regs true.intro _ f₆,
  { convert (assume_spec _ _ f₅) using 0,
    { simp only [concretizes_iff] },
    { refine of_le (le_trans (le_trans l₁ l₂) (le_trans l₃ l₄)) pre },
    { refine sat_of_le (le_trans l₃ l₄) _,
      obtain ⟨l, r⟩ := prod.eq_iff_fst_eq_snd_eq.1 f₂, simp only at l r, rw [← l, ← r], clear l, clear r,
      refine sat_mk_not (by rw [prod.mk.eta]) _,
      obtain ⟨l, r⟩ := prod.eq_iff_fst_eq_snd_eq.1 f₁, simp only at l r, rw [← l, ← r], clear l, clear r,
      refine doJMP_spec (by rw [prod.mk.eta]) (pre.regs_ok dst) (pre.regs_ok src) } },
  rcases ih₁ with ⟨vc₁, vc₁_sat, vc₁_sound⟩,
  rcases ih₂ with ⟨vc₂, vc₂_sat, vc₂_sound⟩,
  existsi (vc₁ && vc₂),
  split,
  { obtain ⟨l, r⟩ := prod.eq_iff_fst_eq_snd_eq.1 f₇, simp only at l r, rw [← l, ← r], clear l, clear r,
    refine sat_mk_and (by rw [prod.mk.eta]) _ vc₂_sat,
    refine sat_of_le (le_trans l₅ l₆) vc₁_sat },
  { rintros ⟨⟩ vcs_true,
    simp only [band_eq_true_eq_eq_tt_and_eq_tt] at vcs_true,
    rcases vcs_true with ⟨⟨⟩, ⟨⟩⟩,
    simp only [eq_self_iff_true, to_bool_iff, forall_true_left, band_tt] at vc₁_sound,
    simp only [bnot_eq_true_eq_eq_ff, bool.to_bool_not, eq_self_iff_true, to_bool_ff_iff, forall_true_left, band_tt] at vc₂_sound,
    cases cond : bpf.JMP.doJMP op (regs dst) (regs src),
    case tt {
      clear vc₂_sound,
      obtain ⟨as_ok, tail⟩ := vc₁_sound cond,
      refine ⟨as_ok, _⟩,
      apply bpf.cfg.safe_from_state_of_det_step tail _ (bpf.cfg.step_jmp_x_det fetch_i),
      have step := bpf.cfg.step.JMP_X fetch_i rfl,
      rw [cond] at step,
      exact step },
    case ff {
      clear vc₁_sound,
      obtain ⟨as_ok, tail⟩ := vc₂_sound cond,
      refine ⟨as_ok, _⟩,
      apply bpf.cfg.safe_from_state_of_det_step tail _ (bpf.cfg.step_jmp_x_det fetch_i),
      have step := bpf.cfg.step.JMP_X fetch_i rfl,
      rw [cond] at step,
      exact step } }
end

theorem step_jmp64_k_correct
  {cfg : CFG χ η} {k : symstate β η → state γ β}
  (k_inc : ∀ s, increasing (k s)) (ih : se_correct cfg ⊤ k)
  {op : JMP} {dst : reg} {imm : lsbvector 64} {if_true if_false : η} :
    se_correct cfg (λ s, lookup s.current cfg.code = some (instr.JMP_K op dst imm if_true if_false))
               (step_jmp64_k cfg k op dst imm if_true if_false) :=
begin
  intros _ _ vc _ _ _ _ fetch_i pre mk,
  simp only [step_jmp64_k, state_t.run_bind] at mk,
  cases f₀ : (mk_const imm : state γ β).run g with const g₀,
  cases f₁ : (doJMP op (abs.regs dst) const).run g₀ with eq g₁,
  cases f₂ : (mk_not eq).run g₁ with neq g₂,
  cases f₃ : (assume_ eq abs).run g₂ with truestate g₃,
  cases f₄ : (k {current := if_true, ..truestate}).run g₃ with true_condition g₄,
  cases f₅ : (assume_ neq abs).run g₄ with falsestate g₅,
  cases f₆ : (k {current := if_false, ..falsestate}).run g₅ with false_condition g₆,
  cases f₇ : (mk_and true_condition false_condition).run g₆ with result g₆,
  simp only [has_bind.bind, id_bind] at mk,
  rw [f₀, f₁, f₂, f₃, f₄, f₅, f₆, f₇] at mk,
  cases mk, clear mk,

  have l₀ : g ≤ g₀,
  { obtain ⟨-, r⟩ := prod.eq_iff_fst_eq_snd_eq.1 f₀, simp only at r, rw [← r],
    apply le_mk_const },
  have l₁ : g₀ ≤ g₁,
  { obtain ⟨-, r⟩ := prod.eq_iff_fst_eq_snd_eq.1 f₁, simp only at r, rw [← r],
    apply doJMP_increasing },
  have l₂ : g₁ ≤ g₂,
  { obtain ⟨-, r⟩ := prod.eq_iff_fst_eq_snd_eq.1 f₂, simp only at r, rw [← r],
    apply le_mk_not },
  have l₃ : g₂ ≤ g₃,
  { obtain ⟨-, r⟩ := prod.eq_iff_fst_eq_snd_eq.1 f₃, simp only at r, rw [← r],
    apply assume_increasing },
  have l₄ : g₃ ≤ g₄,
  { obtain ⟨-, r⟩ := prod.eq_iff_fst_eq_snd_eq.1 f₄, simp only at r, rw [← r],
    apply k_inc },
  have l₅ : g₄ ≤ g₅,
  { obtain ⟨-, r⟩ := prod.eq_iff_fst_eq_snd_eq.1 f₅, simp only at r, rw [← r],
    apply assume_increasing },
  have l₆ : g₅ ≤ g₆,
  { obtain ⟨-, r⟩ := prod.eq_iff_fst_eq_snd_eq.1 f₆, simp only at r, rw [← r],
    apply k_inc },
  have l₇ : g₆ ≤ g',
  { obtain ⟨-, r⟩ := prod.eq_iff_fst_eq_snd_eq.1 f₇, simp only at r, rw [← r],
    apply le_mk_and },

  rename ih → ih₁,
  have ih₂ := ih₁,
  specialize @ih₁ g₃ g₄ true_condition {current := if_true, ..truestate} asserts ((bpf.JMP.doJMP op (regs dst) imm.nth) && assumes) regs true.intro _ f₄,
  { convert (assume_spec _ _ f₃) using 0,
    { simp only [concretizes_iff] },
    { refine of_le (le_trans (le_trans l₀ l₁) l₂) pre },
    { obtain ⟨-, r⟩ := prod.eq_iff_fst_eq_snd_eq.1 f₂, simp only at r, rw [← r], clear r,
      obtain ⟨l, r⟩ := prod.eq_iff_fst_eq_snd_eq.1 f₁, simp only at l r, rw [← l, ← r], clear l, clear r,
      obtain ⟨l, r⟩ := prod.eq_iff_fst_eq_snd_eq.1 f₀, simp only at l r, rw [← l, ← r], clear l, clear r,
      refine sat_of_le le_mk_not _,
      apply doJMP_spec,
      { rw [prod.mk.eta] },
      { refine sat_of_le le_mk_const _,
        apply pre.regs_ok dst },
      { apply sat_mk_const,
        rw [prod.mk.eta] } } },
  specialize @ih₂ g₅ g₆ false_condition {current := if_false, ..falsestate} asserts (!(bpf.JMP.doJMP op (regs dst) imm.nth) && assumes) regs true.intro _ f₆,
  { convert (assume_spec _ _ f₅) using 0,
    { simp only [concretizes_iff] },
    { refine of_le (le_trans (le_trans (le_trans l₀ l₁) l₂) (le_trans l₃ l₄)) pre },
    { refine sat_of_le (le_trans l₃ l₄) _,
      obtain ⟨l, r⟩ := prod.eq_iff_fst_eq_snd_eq.1 f₂, simp only at l r, rw [← l, ← r], clear l, clear r,
      refine sat_mk_not (by rw [prod.mk.eta]) _,
      obtain ⟨l, r⟩ := prod.eq_iff_fst_eq_snd_eq.1 f₁, simp only at l r, rw [← l, ← r], clear l, clear r,
      obtain ⟨l, r⟩ := prod.eq_iff_fst_eq_snd_eq.1 f₀, simp only at l r, rw [← l, ← r], clear l, clear r,
      apply doJMP_spec,
      { rw [prod.mk.eta] },
      { refine sat_of_le le_mk_const _,
        apply pre.regs_ok dst },
      { apply sat_mk_const,
        rw [prod.mk.eta] } } },
  rcases ih₁ with ⟨vc₁, vc₁_sat, vc₁_sound⟩,
  rcases ih₂ with ⟨vc₂, vc₂_sat, vc₂_sound⟩,
  existsi (vc₁ && vc₂),
  split,
  { obtain ⟨l, r⟩ := prod.eq_iff_fst_eq_snd_eq.1 f₇, simp only at l r, rw [← l, ← r], clear l, clear r,
    refine sat_mk_and (by rw [prod.mk.eta]) _ vc₂_sat,
    refine sat_of_le (le_trans l₅ l₆) vc₁_sat },
  { rintros ⟨⟩ vcs_true,
    simp only [band_eq_true_eq_eq_tt_and_eq_tt] at vcs_true,
    rcases vcs_true with ⟨⟨⟩, ⟨⟩⟩,
    simp only [eq_self_iff_true, to_bool_iff, forall_true_left, band_tt] at vc₁_sound,
    simp only [bnot_eq_true_eq_eq_ff, bool.to_bool_not, eq_self_iff_true, to_bool_ff_iff, forall_true_left, band_tt] at vc₂_sound,
    cases cond : bpf.JMP.doJMP op (regs dst) imm.nth,
    case tt {
      clear vc₂_sound,
      obtain ⟨as_ok, tail⟩ := vc₁_sound cond,
      refine ⟨as_ok, _⟩,
      apply bpf.cfg.safe_from_state_of_det_step tail _ (bpf.cfg.step_jmp_k_det fetch_i),
      have step := bpf.cfg.step.JMP_K fetch_i rfl,
      rw [cond] at step,
      exact step },
    case ff {
      clear vc₁_sound,
      obtain ⟨as_ok, tail⟩ := vc₂_sound cond,
      refine ⟨as_ok, _⟩,
      apply bpf.cfg.safe_from_state_of_det_step tail _ (bpf.cfg.step_jmp_k_det fetch_i),
      have step := bpf.cfg.step.JMP_K fetch_i rfl,
      rw [cond] at step,
      exact step } }
end

theorem ALU_check_spec {g g' : γ} {dst src cond : β} {dst_c src_c : i64} {op : bpf.ALU} :
  (ALU_check op dst src).run g = (cond, g') →
  sat g dst (bv_sig dst_c) →
  sat g src (bv_sig src_c) →
  sat g' cond (bv1 (bpf.ALU.ALU_check op dst_c src_c)) :=
begin
  intros mk sat₁ sat₂,
  cases op,
  case DIV {
    simp only [se.ALU_check, state_t.run_bind, state_t.run_pure, state_t.run_map, state_t.run_get] at mk,
    convert (sat_mk_redor mk sat₂),
    rw [bv.any_eq_to_bool_nonzero],
    refl },
  case MOD {
    simp only [se.ALU_check, state_t.run_bind, state_t.run_pure, state_t.run_map, state_t.run_get] at mk,
    convert (sat_mk_redor mk sat₂),
    rw [bv.any_eq_to_bool_nonzero],
    refl },
  all_goals {
    simp only [ALU_check, state_t.run_map] at mk,
    apply sat_mk_true mk <|> apply sat_mk_false mk }
end

theorem lift2_denote_sound {g g' : γ} {e₁ e₂ e₃ : β} {v₁ v₂ : i64} {f : i64 → i64 → i64} :
  (lift2_denote f e₁ e₂).run g = (e₃, g') →
  sat g  e₁ (⟨64, v₁⟩ : Σ n, fin n → bool) →
  sat g  e₂ (⟨64, v₂⟩ : Σ n, fin n → bool) →
  sat g' e₃ (⟨64, f v₁ v₂⟩ : Σ n, fin n → bool) :=
begin
  intros mk sat₁ sat₂,
  simp only [lift2_denote, denote_sound sat₁, denote_sound sat₂, erased.bind_eq_out, erased.out_mk] at mk,
  have sat₃ := sat_mk_var mk,
  simp only [erased.out_mk] at sat₃,
  exact sat₃
end

theorem doALU_spec {g g' : γ} {dst src val : β} {dst_c src_c : i64} {op : bpf.ALU} :
  (doALU op dst src).run g = (val, g') →
  sat g dst (bv_sig dst_c) →
  sat g src (bv_sig src_c) →
  sat g' val (bv_sig (bpf.ALU.doALU64 op dst_c src_c)) :=
begin
  intros mk sat₁ sat₂,
  cases op; simp only [doALU, state_t.run_map] at mk,
  case NEG { exact sat_mk_neg mk sat₁ },
  case ADD { exact sat_mk_add mk sat₁ sat₂ },
  case MOV { cases mk, exact sat₂ },
  case OR  { exact sat_mk_or mk sat₁ sat₂ },
  case AND { exact sat_mk_and mk sat₁ sat₂ },
  case DIV { exact sat_mk_udiv mk sat₁ sat₂ },
  case XOR { exact sat_mk_xor mk sat₁ sat₂ },
  case SUB { exact sat_mk_sub mk sat₁ sat₂ },
  case MUL { exact sat_mk_mul mk sat₁ sat₂ },
  case LSH { exact sat_mk_shl mk sat₁ sat₂ },
  case RSH { exact sat_mk_lshr mk sat₁ sat₂ },
  case ARSH { exact sat_mk_ashr mk sat₁ sat₂ },
  all_goals { exact lift2_denote_sound mk sat₁ sat₂ }
end

/--
  step_alu64_x is a correct symbolic evaluator when the current instruction is ALU64_X and
  the continuation is correct for any state.
-/
theorem step_alu64_x_correct
  {cfg : CFG χ η} {k : symstate β η → state γ β}
  (k_inc : ∀ s, increasing (k s)) (ih : se_correct cfg ⊤ k)
  {op : ALU} {dst src : reg} {next : η} :
    se_correct cfg (λ s, lookup s.current cfg.code = some (instr.ALU64_X op dst src next))
               (step_alu64_x cfg k op dst src next) :=
begin
  intros g g' c abs asserts assumes regs fetch_i pre mk,
  simp only [step_alu64_x, state_t.run_bind] at mk,
  rcases f₁ : (ALU_check op (abs.regs dst) (abs.regs src)).run g with ⟨check, g₁⟩,
  cases f₂ : (assert check abs).run g₁ with s' g₂,
  rcases f₃ : (doALU op (abs.regs dst) (abs.regs src)).run g₂ with ⟨val, g₃⟩,
  cases f₄ : (k {regs := function.update abs.regs dst val,
                 current := next, ..s'}).run g₃ with vc' g₄,
  simp only [(>>=), id_bind] at mk,
  rw [f₁, f₂, f₃, f₄] at mk, cases mk, clear mk,

  have l₁ : g ≤ g₁,
  { obtain ⟨-, r⟩ := prod.eq_iff_fst_eq_snd_eq.1 f₁, simp only at r, rw [← r],
    apply ALU_check_increasing },
  have l₂ : g₁ ≤ g₂,
  { obtain ⟨-, r⟩ := prod.eq_iff_fst_eq_snd_eq.1 f₂, simp only at r, rw [← r],
    apply assert_increasing },
  have l₃ : g₂ ≤ g₃,
  { obtain ⟨-, r⟩ := prod.eq_iff_fst_eq_snd_eq.1 f₃, simp only at r, rw [← r],
    apply doALU_increasing },

  have h₁ := ALU_check_spec f₁ (pre.regs_ok dst) (pre.regs_ok src),
  have h₂ := assert_spec (of_le l₁ pre) h₁ f₂,
  have h₃ := doALU_spec f₃ (factory.sat_of_le (le_trans l₁ l₂) (pre.regs_ok dst))
                           (factory.sat_of_le (le_trans l₁ l₂) (pre.regs_ok src)),
  specialize @ih _ _ c _ (asserts && (bimplies assumes (bpf.ALU.ALU_check op (regs dst) (regs src)))) assumes (function.update regs dst (bpf.ALU.doALU op (regs dst) (regs src))) true.intro _ f₄,
  { apply concretizes.mk,
    { exact sat_of_le l₃ h₂.asserts_ok },
    { exact sat_of_le l₃ h₂.assumes_ok },
    { intros r,
      simp only [function.update],
      split_ifs,
      { subst_vars,
        exact h₃ },
      { exact sat_of_le (le_trans (le_trans l₁ l₂) l₃) (pre.regs_ok r) } } },
  { rcases ih with ⟨vc, vc_sat, vc_sound⟩,
    refine ⟨vc, ⟨vc_sat, _⟩⟩,
    rintros ⟨⟩ ⟨⟩,
    obtain ⟨as_ok, tail⟩ := vc_sound rfl rfl, clear vc_sound,
    simp only [bool.to_bool_not, band_eq_true_eq_eq_tt_and_eq_tt] at as_ok,
    rcases as_ok with ⟨⟨⟩, this_assert_ok⟩,
    refine ⟨rfl, _⟩,
    apply bpf.cfg.safe_from_state_of_det_step tail _ (bpf.cfg.step_alu64_x_det fetch_i),
    refine bpf.cfg.step.ALU64_X fetch_i _ rfl,
    simp only [bimplies, bnot_eq_true_eq_eq_ff, to_bool_ff_iff] at this_assert_ok,
    exact this_assert_ok }
end

theorem step_alu64_k_correct
  {cfg : CFG χ η} {k : symstate β η → state γ β}
  (k_inc : ∀ s, increasing (k s)) (ih : se_correct cfg ⊤ k)
  {op : ALU} {dst : reg} {imm : lsbvector 64} {next : η} :
    se_correct cfg (λ s, lookup s.current cfg.code = some (instr.ALU64_K op dst imm next))
               (step_alu64_k cfg k op dst imm next) :=
begin
  intros g g' c abs asserts assumes regs fetch_i pre mk,
  simp only [step_alu64_k, state_t.run_bind] at mk,
  cases f₁ : (mk_const imm : state γ β).run g with const g₁,
  rcases f₂ : (ALU_check op (abs.regs dst) const).run g₁ with ⟨check, g₂⟩,
  cases f₃ : (assert check abs).run g₂ with s' g₃,
  rcases f₄ : (doALU op (abs.regs dst) const).run g₃ with ⟨val, g₄⟩,
  cases f₅ : (k {regs := function.update abs.regs dst val,
                 current := next, ..s'}).run g₄ with vc' g₅,
  simp only [(>>=), id_bind] at mk,
  rw [f₁, f₂, f₃, f₄, f₅] at mk, cases mk, clear mk,

  have l₁ : g ≤ g₁,
  { obtain ⟨-, r⟩ := prod.eq_iff_fst_eq_snd_eq.1 f₁, simp only at r, rw [← r],
    apply le_mk_const },
  have l₂ : g₁ ≤ g₂,
  { obtain ⟨-, r⟩ := prod.eq_iff_fst_eq_snd_eq.1 f₂, simp only at r, rw [← r],
    apply ALU_check_increasing },
  have l₃ : g₂ ≤ g₃,
  { obtain ⟨-, r⟩ := prod.eq_iff_fst_eq_snd_eq.1 f₃, simp only at r, rw [← r],
    apply assert_increasing },
  have l₄ : g₃ ≤ g₄,
  { obtain ⟨-, r⟩ := prod.eq_iff_fst_eq_snd_eq.1 f₄, simp only at r, rw [← r],
    apply doALU_increasing },

  have h₂ := ALU_check_spec f₂ (sat_of_le l₁ $ pre.regs_ok dst) (sat_mk_const f₁),
  have h₃ := assert_spec (of_le (le_trans l₁ l₂) pre) h₂ f₃,
  have h₄ := doALU_spec f₄ (factory.sat_of_le (le_trans l₁ (le_trans l₂ l₃)) (pre.regs_ok dst))
                           (factory.sat_of_le (le_trans l₂ l₃) (sat_mk_const f₁)),

  specialize @ih _ _ c _ (asserts && (bimplies assumes (bpf.ALU.ALU_check op (regs dst) imm.nth))) assumes (function.update regs dst (bpf.ALU.doALU op (regs dst) imm.nth)) true.intro _ f₅,
  { constructor,
    { exact sat_of_le l₄ h₃.asserts_ok },
    { exact sat_of_le l₄ h₃.assumes_ok },
    { intros r,
      simp only [function.update],
      split_ifs,
      { subst_vars,
        exact h₄ },
      { exact sat_of_le (le_trans (le_trans l₁ l₂) (le_trans l₃ l₄)) (pre.regs_ok r) } } },
  { rcases ih with ⟨vc, vc_sat, vc_sound⟩,
    refine ⟨vc, ⟨vc_sat, _⟩⟩,
    rintros ⟨⟩ ⟨⟩,
    obtain ⟨as_ok, tail⟩ := vc_sound rfl rfl, clear vc_sound,
    simp only [bool.to_bool_not, band_eq_true_eq_eq_tt_and_eq_tt] at as_ok,
    rcases as_ok with ⟨⟨⟩, this_assert_ok⟩,
    refine ⟨rfl, _⟩,
    apply bpf.cfg.safe_from_state_of_det_step tail _ (bpf.cfg.step_alu64_k_det fetch_i),
    refine bpf.cfg.step.ALU64_K fetch_i _ rfl,
    simp only [bimplies, bnot_eq_true_eq_eq_ff, to_bool_ff_iff] at this_assert_ok,
    exact this_assert_ok }
end

/-- step_symeval is correct for any state when the continuation is correct for any state. -/
theorem step_symeval_correct
  {cfg : CFG χ η} {k : symstate β η → state γ β}
  (k_inc : ∀ s, increasing (k s)) (ih : se_correct cfg ⊤ k) :
    se_correct cfg ⊤ (step_symeval cfg k) :=
begin
  simp only [step_symeval],
  rintros _ _ vc _ _ _ _ ⟨⟩ pre mk,
  simp only at mk,
  cases fetch_i : lookup abs.current cfg.code; rw [fetch_i] at mk,
  case none {
    exact die_correct true.intro pre mk },
  case some : instr {
    cases instr; simp only [step_symeval._match_1] at mk,
    case ALU64_X { exact step_alu64_x_correct k_inc ih fetch_i pre mk },
    case ALU64_K { exact step_alu64_k_correct k_inc ih fetch_i pre mk },
    case JMP_X { exact step_jmp64_x_correct k_inc ih fetch_i pre mk },
    case JMP_K { exact step_jmp64_k_correct k_inc ih fetch_i pre mk },
    case STX {
      exact die_correct true.intro pre mk },
    case Exit {
      simp only [state_t.run_pure] at mk,
      cases mk, clear mk,
      refine ⟨asserts, ⟨pre.asserts_ok, _⟩⟩,
      intros assumes_true asserts_true,
      refine ⟨asserts_true, _⟩,
      apply bpf.cfg.safe_from_state_of_det_step bpf.cfg.safe_from_exited (bpf.cfg.step.Exit fetch_i) (bpf.cfg.step_exit_det fetch_i) } }
end

theorem symeval_correct (cfg : CFG χ η) (fuel : ℕ) :
  se_correct cfg ⊤ (symeval cfg fuel : symstate β η → state γ β) :=
begin
  induction fuel,
  case zero { exact infeasible_correct },
  case succ : _ ih { exact step_symeval_correct symeval_increasing ih }
end

/-- If the verification conditions evaluate to tt, then the program is safe. -/
theorem vcgen_spec {cfg : CFG χ η} {fuel : ℕ} {g g' : γ} {vc : β} {regs : erased (vector i64 bpf.nregs)} :
  (@vcgen χ η β γ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ cfg fuel regs).run g = (vc, g') →
  ∃ (vc_b : bool),
    sat g' vc (bv1 vc_b) ∧
    (vc_b = tt →
     bpf.cfg.safe_from_state cfg (bpf.cfg.state.running cfg.entry (reg.of_vector regs.out))) :=
begin
  intros mk,
  let init := ((initial_symstate cfg regs).run g).1,
  let g' := ((initial_symstate cfg regs).run g).2,
  have correct := symeval_correct cfg fuel,
  obtain ⟨vc_b, sat₁, sound⟩ := @correct g' _ (_ : β) init tt tt (reg.of_vector regs.out) true.intro _ _,
  { refine ⟨vc_b, ⟨sat₁, _⟩⟩,
    rintros ⟨⟩,
    obtain ⟨-, tail⟩ := sound rfl rfl,
    simp only [initial_symstate_current] at tail,
    exact tail },
  { apply @initial_symstate_spec _ _ _ _ _,
    rw [prod.mk.eta] },
  simp only [g', init],
  simp only [vcgen, state_t.run_bind] at mk,
  exact mk
end

end proof
end se
end cfg
end bpf
