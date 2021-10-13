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
  [smt.urem_factory β γ]

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
structure concretizes (g : γ) (abs : symstate β η) (asserts assumes : bool) (concrete : runstate η) : Prop :=
(asserts_ok  : sat g abs.assertions (bv1 asserts))
(assumes_ok  : sat g abs.assumptions (bv1 assumes))
(regs_ok     : ∀ (r : reg), sat g (abs.regs r) (concrete.regs r))
(pc_ok       : abs.current = concrete.pc)
(next_rng_ok : abs.next_rng = concrete.next_rng)

namespace concretizes

theorem of_le {abs : symstate β η} {asserts assumes : bool} {concrete : runstate η} {g₁ g₂ : γ} :
  g₁ ≤ g₂ →
  concretizes g₁ abs asserts assumes concrete →
  concretizes g₂ abs asserts assumes concrete :=
begin
  intros l c,
  cases c,
  constructor,
  { exact sat_of_le l c_asserts_ok },
  { exact sat_of_le l c_assumes_ok },
  { intros r,
    apply sat_of_le l,
    tauto },
  { assumption },
  { assumption }
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

theorem assert_spec {s s' : symstate β η} {g g' : γ} {c : β} {as asserts assumes : bool} {concrete : runstate η} :
  concretizes g s asserts assumes concrete →
  sat g c (bv1 as) →
  (assert c s).run g = (s', g') →
  concretizes g' s' (asserts && (bimplies assumes as)) assumes concrete :=
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
  { exact λ r, sat_of_le inc (pre.regs_ok r) },
  { apply pre.pc_ok },
  { apply pre.next_rng_ok }
end

theorem assume_spec {s s' : symstate β η} {g g' : γ} {c : β} {as asserts assumes : bool} {concrete : runstate η} :
  concretizes g s asserts assumes concrete →
  sat g c (bv1 as) →
  (assume_ c s).run g = (s', g') →
  concretizes g' s' asserts (as && assumes) concrete :=
begin
  intros pre sat mk,
  have inc : g ≤ _ := assume_increasing c s,
  rw [mk] at inc,
  simp only [assume_, state_t.run_bind] at mk,
  cases mk, clear mk,
  apply concretizes.mk,
  { exact sat_of_le inc pre.asserts_ok },
  { exact sat_mk_and (by rw [prod.mk.eta]) sat pre.assumes_ok },
  { exact λ r, sat_of_le inc (pre.regs_ok r) },
  { apply pre.pc_ok },
  { apply pre.next_rng_ok }
end

/-- The actual symbolic evaluation routine is continuation-based, so the
    correctness of one of these functions inductively depends on the correctness
    of the continuation. -/
def se_correct (cfg : CFG χ η) (o : oracle) (p : set (symstate β η)) (k : symstate β η → state γ β) : Prop :=
∀ ⦃g g' : γ⦄ ⦃c : β⦄ ⦃abs : symstate β η⦄ ⦃asserts assumes : bool⦄ ⦃concrete : runstate η⦄,
  -- If the abstract state is one we care about, and
  abs ∈ p →
  -- the abstract state concretizes to a legitimate state, and
  concretizes g abs asserts assumes concrete →
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
      bpf.cfg.safe_from_state cfg o (state.running concrete))

namespace se_correct

theorem weaken {cfg : CFG χ η} {o : oracle} {p p' : set (symstate β η)} {k : symstate β η → state γ β} :
  se_correct cfg o p k →
  p' ⊆ p →
  se_correct cfg o p' k :=
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
    case instr.Exit {
      apply increasing_bind; intros,
      apply le_mk_const,
      apply increasing_bind; intros,
      apply assert_increasing,
      apply increasing_pure } }
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

theorem initial_regs_increasing : ∀ {n : ℕ} {r : erased (vector value n)},
  increasing (se.initial_regs r : state γ (vector (symvalue β) n))
| 0       := λ _, by apply increasing_pure
| (n + 1) := by {
  intro regs,
  simp only [se.initial_regs],
  apply increasing_bind,
  { apply symvalue.le_mk_unknown },
  intro c,
  apply increasing_bind,
  { apply @initial_regs_increasing },
  intro c',
  apply increasing_pure }

theorem initial_regs_spec : ∀ {n : ℕ} (regs : erased (vector value n)) {regs' : vector (symvalue β) n} {g g' : γ},
  (se.initial_regs regs).run g = (regs', g') →
  ∀ {r : fin n},
    sat g' (regs'.nth r) (regs.out.nth r)
| 0       _    _     _ _  _   := fin.elim0
| (n + 1) regs regs' g g' mk' := λ r, by {
  simp only [se.initial_regs, state_t.run_bind] at mk',
  cases mk', clear mk',
  refine fin.cases _ _ r,
  { simp only [vector.nth_zero, vector.cons_head],
    refine sat_of_le (by apply initial_regs_increasing) _,
    rw [← erased.out_mk (regs.out.head)],
    apply symvalue.sat_mk_unknown,
    simp only [vector.nth_zero, erased.map, erased.bind_eq_out, prod.mk.eta] },
  { simp only [vector.nth_cons_succ],
    intros i,
    simp only [erased.map, erased.bind_eq_out, erased.out_mk, erased.mk_out, function.comp],
    rw [← vector.cons_head_tail regs.out, vector.tail_cons, vector.head_cons, vector.nth_cons_succ],
    rw [← erased.out_mk (regs.out.tail)],
    apply initial_regs_spec,
    simp only [erased.mk_out, erased.out_mk, prod.mk.eta] } }

theorem initial_state_increasing (cfg : CFG χ η) (o : erased oracle) :
  increasing (initial_symstate cfg o : state γ (symstate β η)) :=
begin
  simp only [initial_symstate],
  apply increasing_bind,
  apply le_mk_const,
  intro c, apply increasing_bind,
  apply initial_regs_increasing,
  intro c, apply increasing_pure
end

theorem initial_symstate_spec
  (g : γ) {g' : γ} {s : symstate β η} (cfg : CFG χ η) (o : erased oracle) :
    (initial_symstate cfg o).run g = (s, g') →
    concretizes g' s tt tt ⟨cfg.entry, o.out.initial_regs, 0⟩ :=
begin
  intros mk,
  simp only [initial_symstate, state_t.run_bind] at mk,
  injection mk with h₁ h₂, subst h₁, subst h₂, clear mk,
  apply concretizes.mk; simp only,
  { exact sat_of_le (by apply initial_regs_increasing) (sat_mk_true (by rw [prod.mk.eta])) },
  { exact sat_of_le (by apply initial_regs_increasing) (sat_mk_true (by rw [prod.mk.eta])) },
  { simp only [reg.of_vector],
    intros r,
    have : o.out.initial_regs r = (reg.to_vector o.out.initial_regs).nth r.to_fin,
    { cases r; refl },
    rw this,
    have h := initial_regs_spec ((λ (o' : oracle), reg.to_vector o'.initial_regs) <$> o) _,
    simp only [erased.map_out, erased.map_def] at h,
    apply h,
    swap 2,
    rw [prod.mk.eta] },
  { refl }
end

theorem initial_symstate_current {g : γ} {cfg : CFG χ η} {o : erased oracle} :
  ((initial_symstate cfg o : state γ (symstate β η)).run g).1.current = (CFG.entry cfg) :=
begin
  simp only [initial_symstate, state_t.run_bind],
  refl
end

/-- "die" is a correct symbolic evaluator (that rejects everything). -/
theorem die_correct {cfg : CFG χ η} {o : oracle} : se_correct cfg o ⊤ (λ (_ : symstate β η), (die : state γ β)) :=
begin
  rintros _ _ _ _ _ _ _ ⟨⟩ assumes_sat die_mk,
  existsi ff,
  split,
  { simp only [die, state_t.run_map, state_t.run_get] at die_mk,
    apply sat_mk_false die_mk },
  { tauto }
end

theorem infeasible_correct {cfg : CFG χ η} {o : oracle} : se_correct cfg o ⊤ (infeasible : symstate β η → state γ β) :=
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

/--
  step_jmp64_x is a correct symbolic evaluator when the current instruction is JMP_X and
  the continuation is correct for any state.
-/
theorem step_jmp64_x_correct
  {cfg : CFG χ η} {o : oracle} {k : symstate β η → state γ β}
  (k_inc : ∀ s, increasing (k s)) (ih : se_correct cfg o ⊤ k)
  {op : JMP} {dst src : reg} {if_true if_false : η} :
    se_correct cfg o (λ s, lookup s.current cfg.code = some (instr.JMP_X op dst src if_true if_false))
               (step_jmp64_x cfg k op dst src if_true if_false) :=
begin
  intros _ _ vc _ _ _ _ fetch_i pre mk,
  simp only [step_jmp64_x, state_t.run_bind] at mk,
  cases f₁₀ : (symvalue.doJMP_check op (abs.regs dst) (abs.regs src)).run g with check g₁₀,
  cases f₁₁ : (assert check abs).run g₁₀ with s' g₁₁,
  cases f₁ : (symvalue.doJMP op (s'.regs dst) (s'.regs src)).run g₁₁ with eq g₁,
  cases f₂ : (mk_not eq).run g₁ with neq g₂,
  cases f₃ : (assume_ eq s').run g₂ with truestate g₃,
  cases f₄ : (k {current := if_true, ..truestate}).run g₃ with true_condition g₄,
  cases f₅ : (assume_ neq s').run g₄ with falsestate g₅,
  cases f₆ : (k {current := if_false, ..falsestate}).run g₅ with false_condition g₆,
  cases f₇ : (mk_and true_condition false_condition).run g₆ with result g₆,
  simp only [has_bind.bind, id_bind] at mk,
  rw [f₁₀, f₁₁, f₁, f₂, f₃, f₄, f₅, f₆, f₇] at mk,
  cases mk, clear mk,

  have l₁₀ : g ≤ g₁₀,
  { obtain ⟨-, r⟩ := prod.eq_iff_fst_eq_snd_eq.1 f₁₀, simp only at r, rw [← r],
    apply symvalue.doJMP_check_increasing },
  have l₁₁ : g₁₀ ≤ g₁₁,
  { obtain ⟨-, r⟩ := prod.eq_iff_fst_eq_snd_eq.1 f₁₁, simp only at r, rw [← r],
    apply assert_increasing },
  have l₁ : g₁₁ ≤ g₁,
  { obtain ⟨-, r⟩ := prod.eq_iff_fst_eq_snd_eq.1 f₁, simp only at r, rw [← r],
    apply symvalue.doJMP_increasing },
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

  have h₁₀ := symvalue.sat_doJMP_check f₁₀ (pre.regs_ok dst) (pre.regs_ok src),
  have h₁₁ := assert_spec (of_le l₁₀ pre) h₁₀ f₁₁,
  have h₁ := symvalue.sat_doJMP f₁ (h₁₁.regs_ok dst) (h₁₁.regs_ok src),
  have h₂ := sat_mk_not f₂ h₁,
  have h₃ := assume_spec (of_le (le_trans l₁ l₂) h₁₁) (sat_of_le l₂ h₁) f₃,
  simp only [bv.not] at h₂,
  have h₅ := assume_spec (of_le (le_trans (le_trans l₁ l₂) (le_trans l₃ l₄)) h₁₁) (sat_of_le (le_trans l₃ l₄) h₂) f₅,

  rename ih → ih₁,
  have ih₂ := ih₁,
  specialize @ih₁ g₃ g₄ true_condition _ (asserts && bimplies assumes (op.doJMP_check (concrete.regs dst) (concrete.regs src))) ((bpf.JMP.doJMP op (concrete.regs dst) (concrete.regs src)) && assumes) { pc := if_true, ..concrete } true.intro _ f₄,
  { apply concretizes.mk,
    { apply h₃.asserts_ok },
    { apply h₃.assumes_ok },
    { intros r,
      apply h₃.regs_ok r },
    { refl },
    { apply h₃.next_rng_ok } },
  specialize @ih₂ g₅ g₆ false_condition _ (asserts && bimplies assumes (op.doJMP_check (concrete.regs dst) (concrete.regs src))) (!(bpf.JMP.doJMP op (concrete.regs dst) (concrete.regs src)) && assumes) { pc := if_false, ..concrete } true.intro _ f₆,
  { apply concretizes.mk,
    { apply h₅.asserts_ok },
    { apply h₅.assumes_ok },
    { intros r,
      apply h₅.regs_ok r },
    { refl },
    { apply h₅.next_rng_ok } },
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
    cases cond : bpf.JMP.doJMP op (concrete.regs dst) (concrete.regs src),
    case tt {
      clear vc₂_sound,
      obtain ⟨as_ok, tail⟩ := vc₁_sound cond,
      simp only [band_eq_true_eq_eq_tt_and_eq_tt, bimplies] at as_ok,
      refine ⟨as_ok.1, _⟩,
      simp only [set.mem_def, pre.pc_ok] at fetch_i,
      apply bpf.cfg.safe_from_state_of_det_step tail _ (bpf.cfg.step_jmp_x_det concrete fetch_i),
      have step := bpf.cfg.step.JMP_X concrete fetch_i as_ok.2 rfl,
      rw [cond] at step,
      exact step },
    case ff {
      clear vc₁_sound,
      obtain ⟨as_ok, tail⟩ := vc₂_sound cond,
      simp only [band_eq_true_eq_eq_tt_and_eq_tt, bimplies] at as_ok,
      refine ⟨as_ok.1, _⟩,
      simp only [set.mem_def, pre.pc_ok] at fetch_i,
      apply bpf.cfg.safe_from_state_of_det_step tail _ (bpf.cfg.step_jmp_x_det concrete fetch_i),
      have step := bpf.cfg.step.JMP_X concrete fetch_i as_ok.2 rfl,
      rw [cond] at step,
      exact step } }
end

theorem step_jmp64_k_correct
  {cfg : CFG χ η} {o : oracle} {k : symstate β η → state γ β}
  (k_inc : ∀ s, increasing (k s)) (ih : se_correct cfg o ⊤ k)
  {op : JMP} {dst : reg} {imm : lsbvector 64} {if_true if_false : η} :
    se_correct cfg o (λ s, lookup s.current cfg.code = some (instr.JMP_K op dst imm if_true if_false))
               (step_jmp64_k cfg k op dst imm if_true if_false) :=
begin
  intros _ _ vc _ _ _ _ fetch_i pre mk,
  simp only [step_jmp64_k, state_t.run_bind] at mk,
  cases f₀₀ : (symvalue.mk_scalar imm : state γ (symvalue β)).run g with const g₀₀,
  cases f₁₀ : (symvalue.doJMP_check op (abs.regs dst) const).run g₀₀ with check g₁₀,
  cases f₁₁ : (assert check abs).run g₁₀ with s' g₁₁,
  cases f₁ : (symvalue.doJMP op (s'.regs dst) const).run g₁₁ with eq g₁,
  cases f₂ : (mk_not eq).run g₁ with neq g₂,
  cases f₃ : (assume_ eq s').run g₂ with truestate g₃,
  cases f₄ : (k {current := if_true, ..truestate}).run g₃ with true_condition g₄,
  cases f₅ : (assume_ neq s').run g₄ with falsestate g₅,
  cases f₆ : (k {current := if_false, ..falsestate}).run g₅ with false_condition g₆,
  cases f₇ : (mk_and true_condition false_condition).run g₆ with result g₆,
  simp only [has_bind.bind, id_bind] at mk,
  rw [f₀₀, f₁₀, f₁₁] at mk,
  simp only at mk,
  rw [f₁, f₂, f₃, f₄, f₅, f₆, f₇] at mk,
  cases mk, clear mk,

  have l₀₀ : g ≤ g₀₀,
  { obtain ⟨-, r⟩ := prod.eq_iff_fst_eq_snd_eq.1 f₀₀, simp only at r, rw [← r],
    apply symvalue.le_mk_scalar },
  have l₁₀ : g₀₀ ≤ g₁₀,
  { obtain ⟨-, r⟩ := prod.eq_iff_fst_eq_snd_eq.1 f₁₀, simp only at r, rw [← r],
    apply symvalue.doJMP_check_increasing },
  have l₁₁ : g₁₀ ≤ g₁₁,
  { obtain ⟨-, r⟩ := prod.eq_iff_fst_eq_snd_eq.1 f₁₁, simp only at r, rw [← r],
    apply assert_increasing },
  have l₁ : g₁₁ ≤ g₁,
  { obtain ⟨-, r⟩ := prod.eq_iff_fst_eq_snd_eq.1 f₁, simp only at r, rw [← r],
    apply symvalue.doJMP_increasing },
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

  have h₀₀ := symvalue.sat_mk_scalar f₀₀,
  have h₁₀ := symvalue.sat_doJMP_check f₁₀ (sat_of_le l₀₀ (pre.regs_ok dst)) h₀₀,
  have h₁₁ := assert_spec (of_le (le_trans l₀₀ l₁₀) pre) h₁₀ f₁₁,
  have h₁ := symvalue.sat_doJMP f₁ (h₁₁.regs_ok dst) (sat_of_le (le_trans l₁₀ l₁₁) h₀₀),
  have h₂ := sat_mk_not f₂ h₁,
  have h₃ := assume_spec (of_le (le_trans l₁ l₂) h₁₁) (sat_of_le l₂ h₁) f₃,
  simp only [bv.not] at h₂,
  have h₅ := assume_spec (of_le (le_trans (le_trans l₁ l₂) (le_trans l₃ l₄)) h₁₁) (sat_of_le (le_trans l₃ l₄) h₂) f₅,

  rename ih → ih₁,
  have ih₂ := ih₁,
  specialize @ih₁ g₃ g₄ true_condition _ (asserts && bimplies assumes (op.doJMP_check (concrete.regs dst) (bpf.value.scalar imm.nth))) ((bpf.JMP.doJMP op (concrete.regs dst) (bpf.value.scalar imm.nth)) && assumes) { pc := if_true, ..concrete } true.intro _ f₄,
  { apply concretizes.mk,
    { apply h₃.asserts_ok },
    { apply h₃.assumes_ok },
    { intros r,
      apply h₃.regs_ok r },
    { refl },
    { apply h₃.next_rng_ok } },
  specialize @ih₂ g₅ g₆ false_condition _ (asserts && bimplies assumes (op.doJMP_check (concrete.regs dst) (bpf.value.scalar imm.nth))) (!(bpf.JMP.doJMP op (concrete.regs dst) (bpf.value.scalar imm.nth)) && assumes) { pc := if_false, ..concrete } true.intro _ f₆,
  { apply concretizes.mk,
    { apply h₅.asserts_ok },
    { apply h₅.assumes_ok },
    { intros r,
      apply h₅.regs_ok r },
    { refl },
    { apply h₅.next_rng_ok } },  rcases ih₁ with ⟨vc₁, vc₁_sat, vc₁_sound⟩,
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
    cases cond : bpf.JMP.doJMP op (concrete.regs dst) (bpf.value.scalar imm.nth),
    case tt {
      clear vc₂_sound,
      obtain ⟨as_ok, tail⟩ := vc₁_sound cond,
      simp only [band_eq_true_eq_eq_tt_and_eq_tt, bimplies] at as_ok,
      refine ⟨as_ok.1, _⟩,
      simp only [set.mem_def, pre.pc_ok] at fetch_i,
      apply bpf.cfg.safe_from_state_of_det_step tail _ (bpf.cfg.step_jmp_k_det _ fetch_i),
      have step := bpf.cfg.step.JMP_K _ fetch_i as_ok.2 rfl,
      rw [cond] at step,
      exact step },
    case ff {
      clear vc₁_sound,
      obtain ⟨as_ok, tail⟩ := vc₂_sound cond,
      simp only [band_eq_true_eq_eq_tt_and_eq_tt, bimplies] at as_ok,
      refine ⟨as_ok.1, _⟩,
      simp only [set.mem_def, pre.pc_ok] at fetch_i,
      apply bpf.cfg.safe_from_state_of_det_step tail _ (bpf.cfg.step_jmp_k_det _ fetch_i),
      have step := bpf.cfg.step.JMP_K _ fetch_i as_ok.2 rfl,
      rw [cond] at step,
      exact step } }
end

/--
  step_alu64_x is a correct symbolic evaluator when the current instruction is ALU64_X and
  the continuation is correct for any state.
-/
theorem step_alu64_x_correct
  {cfg : CFG χ η} {k : symstate β η → state γ β} {o : oracle}
  (k_inc : ∀ s, increasing (k s)) (ih : se_correct cfg o ⊤ k)
  {op : ALU} {dst src : reg} {next : η} :
    se_correct cfg o (λ s, lookup s.current cfg.code = some (instr.ALU64_X op dst src next))
               (step_alu64_x cfg k op dst src next) :=
begin
  intros g g' c abs asserts assumes concrete fetch_i pre mk,
  simp only [step_alu64_x, state_t.run_bind] at mk,
  rcases f₁ : (symvalue.doALU_check op (abs.regs dst) (abs.regs src)).run g with ⟨check, g₁⟩,
  cases f₂ : (assert check abs).run g₁ with s' g₂,
  rcases f₃ : (symvalue.doALU op (abs.regs dst) (abs.regs src)).run g₂ with ⟨val, g₃⟩,
  cases f₄ : (k {regs := function.update abs.regs dst val,
                 current := next, ..s'}).run g₃ with vc' g₄,
  simp only [(>>=), id_bind] at mk,
  rw [f₁, f₂, f₃, f₄] at mk, cases mk, clear mk,

  have l₁ : g ≤ g₁,
  { obtain ⟨-, r⟩ := prod.eq_iff_fst_eq_snd_eq.1 f₁, simp only at r, rw [← r],
    apply symvalue.doALU_check_increasing },
  have l₂ : g₁ ≤ g₂,
  { obtain ⟨-, r⟩ := prod.eq_iff_fst_eq_snd_eq.1 f₂, simp only at r, rw [← r],
    apply assert_increasing },
  have l₃ : g₂ ≤ g₃,
  { obtain ⟨-, r⟩ := prod.eq_iff_fst_eq_snd_eq.1 f₃, simp only at r, rw [← r],
    apply symvalue.doALU_increasing },

  have h₁ := symvalue.sat_doALU_check f₁ (pre.regs_ok dst) (pre.regs_ok src),
  have h₂ := assert_spec (of_le l₁ pre) h₁ f₂,
  have h₃ := symvalue.sat_doALU f₃ (factory.sat_of_le (le_trans l₁ l₂) (pre.regs_ok dst))
                           (factory.sat_of_le (le_trans l₁ l₂) (pre.regs_ok src)),
  specialize @ih _ _ c _
      (asserts && (bimplies assumes (bpf.ALU.doALU_check op (concrete.regs dst) (concrete.regs src))))
      assumes
      { regs := function.update concrete.regs dst (bpf.ALU.doALU op (concrete.regs dst) (concrete.regs src)),
        pc := next,
        ..concrete }
       true.intro _ f₄,
  { apply concretizes.mk,
    { exact sat_of_le l₃ h₂.asserts_ok },
    { exact sat_of_le l₃ h₂.assumes_ok },
    { intros r,
      simp only [function.update],
      split_ifs,
      { subst_vars,
        exact h₃ },
      { exact sat_of_le (le_trans (le_trans l₁ l₂) l₃) (pre.regs_ok r) } },
    { simp only },
    { simp only,
      apply h₂.next_rng_ok } },
  { rcases ih with ⟨vc, vc_sat, vc_sound⟩,
    refine ⟨vc, ⟨vc_sat, _⟩⟩,
    rintros ⟨⟩ ⟨⟩,
    obtain ⟨as_ok, tail⟩ := vc_sound rfl rfl, clear vc_sound,
    simp only [bool.to_bool_not, band_eq_true_eq_eq_tt_and_eq_tt] at as_ok,
    rcases as_ok with ⟨⟨⟩, this_assert_ok⟩,
    refine ⟨rfl, _⟩,
    simp only [set.mem_def, pre.pc_ok] at fetch_i,
    apply bpf.cfg.safe_from_state_of_det_step tail _ (bpf.cfg.step_alu64_x_det concrete fetch_i),
    simp only,
    have h := bpf.cfg.step.ALU64_X concrete fetch_i _ rfl,
    exact h,
    simp only [bimplies, bnot_eq_true_eq_eq_ff, to_bool_ff_iff] at this_assert_ok,
    exact this_assert_ok }
end

theorem step_alu64_k_correct
  {cfg : CFG χ η} {k : symstate β η → state γ β} {o : oracle}
  (k_inc : ∀ s, increasing (k s)) (ih : se_correct cfg o ⊤ k)
  {op : ALU} {dst : reg} {imm : lsbvector 64} {next : η} :
    se_correct cfg o (λ s, lookup s.current cfg.code = some (instr.ALU64_K op dst imm next))
               (step_alu64_k cfg k op dst imm next) :=
begin
  intros g g' c abs asserts assumes concrete fetch_i pre mk,
  simp only [step_alu64_k, state_t.run_bind] at mk,
  cases f₁ : (symvalue.mk_scalar imm : state γ (symvalue β)).run g with const g₁,
  rcases f₂ : (symvalue.doALU_check op (abs.regs dst) const).run g₁ with ⟨check, g₂⟩,
  cases f₃ : (assert check abs).run g₂ with s' g₃,
  rcases f₄ : (symvalue.doALU op (abs.regs dst) const).run g₃ with ⟨val, g₄⟩,
  cases f₅ : (k {regs := function.update abs.regs dst val,
                 current := next, ..s'}).run g₄ with vc' g₅,
  simp only [(>>=), id_bind] at mk,
  rw [f₁, f₂, f₃, f₄, f₅] at mk, cases mk, clear mk,

  have l₁ : g ≤ g₁,
  { obtain ⟨-, r⟩ := prod.eq_iff_fst_eq_snd_eq.1 f₁, simp only at r, rw [← r],
    apply symvalue.le_mk_scalar },
  have l₂ : g₁ ≤ g₂,
  { obtain ⟨-, r⟩ := prod.eq_iff_fst_eq_snd_eq.1 f₂, simp only at r, rw [← r],
    apply symvalue.doALU_check_increasing },
  have l₃ : g₂ ≤ g₃,
  { obtain ⟨-, r⟩ := prod.eq_iff_fst_eq_snd_eq.1 f₃, simp only at r, rw [← r],
    apply assert_increasing },
  have l₄ : g₃ ≤ g₄,
  { obtain ⟨-, r⟩ := prod.eq_iff_fst_eq_snd_eq.1 f₄, simp only at r, rw [← r],
    apply symvalue.doALU_increasing },

  have h₂ := symvalue.sat_doALU_check f₂ (sat_of_le l₁ $ pre.regs_ok dst) (symvalue.sat_mk_scalar f₁),
  have h₃ := assert_spec (of_le (le_trans l₁ l₂) pre) h₂ f₃,
  have h₄ := symvalue.sat_doALU f₄ (factory.sat_of_le (le_trans l₁ (le_trans l₂ l₃)) (pre.regs_ok dst))
                           (factory.sat_of_le (le_trans l₂ l₃) (symvalue.sat_mk_scalar f₁)),

  specialize @ih _ _ c _ (asserts && (bimplies assumes (bpf.ALU.doALU_check op (concrete.regs dst) (bpf.value.scalar imm.nth))))
                         assumes
                         { regs := function.update concrete.regs dst (bpf.ALU.doALU op (concrete.regs dst) (bpf.value.scalar imm.nth)),
                           pc := next,
                          ..concrete }
                         true.intro _ f₅,
  { constructor,
    { exact sat_of_le l₄ h₃.asserts_ok },
    { exact sat_of_le l₄ h₃.assumes_ok },
    { intros r,
      simp only [function.update],
      split_ifs,
      { subst_vars,
        exact h₄ },
      { exact sat_of_le (le_trans (le_trans l₁ l₂) (le_trans l₃ l₄)) (pre.regs_ok r) } },
    { simp only },
    { simp only,
      apply h₃.next_rng_ok } },
  { rcases ih with ⟨vc, vc_sat, vc_sound⟩,
    refine ⟨vc, ⟨vc_sat, _⟩⟩,
    rintros ⟨⟩ ⟨⟩,
    obtain ⟨as_ok, tail⟩ := vc_sound rfl rfl, clear vc_sound,
    simp only [bool.to_bool_not, band_eq_true_eq_eq_tt_and_eq_tt] at as_ok,
    rcases as_ok with ⟨⟨⟩, this_assert_ok⟩,
    refine ⟨rfl, _⟩,
    simp only [set.mem_def, pre.pc_ok] at fetch_i,
    apply bpf.cfg.safe_from_state_of_det_step tail _ (bpf.cfg.step_alu64_k_det _ fetch_i),
    refine bpf.cfg.step.ALU64_K _ fetch_i _ rfl,
    simp only [bimplies, bnot_eq_true_eq_eq_ff, to_bool_ff_iff] at this_assert_ok,
    exact this_assert_ok }
end

theorem step_exit_correct
  {cfg : CFG χ η} {k : symstate β η → state γ β} {o : oracle}
  (k_inc : ∀ s, increasing (k s)) (ih : se_correct cfg o ⊤ k) :
    se_correct cfg o (λ s, lookup s.current cfg.code = some instr.Exit)
               (step_exit cfg k) :=
begin
  intros g g' c abs asserts assumes concrete fetch_i pre mk,
  simp only [step_exit, state_t.run_bind] at mk,
  cases f₁ : ((mk_const1 (abs.regs reg.R0).is_scalar).run g : β × γ) with noleak g',
  cases f₂ : (assert noleak abs).run g' with abs' g'',
  simp only [(>>=), id_bind] at mk,
  rw [f₁, f₂] at mk,
  have l₁ : g ≤ g',
  { obtain ⟨-, r⟩ := prod.eq_iff_fst_eq_snd_eq.1 f₁, simp only at r, rw [← r],
    apply le_mk_const },
  have l₂ : g' ≤ g'',
  { obtain ⟨-, r⟩ := prod.eq_iff_fst_eq_snd_eq.1 f₂, simp only at r, rw [← r],
    apply assert_increasing },
  cases mk,
  have h₁ := sat_mk_const1 f₁,
  have h₂ := assert_spec (of_le l₁ pre) h₁ f₂,
  existsi _,
  refine ⟨h₂.asserts_ok, _⟩,
  intros assumes_true asserts_true,
  simp only [band_eq_true_eq_eq_tt_and_eq_tt] at asserts_true,
  refine ⟨asserts_true.1, _⟩,
  cases asserts_true with asserts_true noleak',
  simp only [assumes_true, bimplies, to_bool_iff] at noleak',
  cases noleak' with return_value return_value_h,
  have return_register_sat := pre.regs_ok reg.R0,
  rw [return_value_h] at return_register_sat,
  generalize hreg0 : concrete.regs reg.R0 = reg_r0,
  rw [hreg0] at return_register_sat,
  cases return_register_sat,
  simp only [set.mem_def, pre.pc_ok] at fetch_i,
  exact bpf.cfg.safe_from_state_of_det_step bpf.cfg.safe_from_exited (bpf.cfg.step.Exit _ fetch_i hreg0) (bpf.cfg.step_exit_det _ fetch_i)
end

/-- step_symeval is correct for any state when the continuation is correct for any state. -/
theorem step_symeval_correct
  {cfg : CFG χ η} {k : symstate β η → state γ β} {o : oracle}
  (k_inc : ∀ s, increasing (k s)) (ih : se_correct cfg o ⊤ k) :
    se_correct cfg o ⊤ (step_symeval cfg k) :=
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
      exact step_exit_correct k_inc ih fetch_i pre mk } }
end

theorem symeval_correct (cfg : CFG χ η) (o : oracle) (fuel : ℕ) :
  se_correct cfg o ⊤ (symeval cfg fuel : symstate β η → state γ β) :=
begin
  induction fuel,
  case zero { exact infeasible_correct },
  case succ : _ ih { exact step_symeval_correct symeval_increasing ih }
end

/-- If the verification conditions evaluate to tt, then the program is safe. -/
theorem vcgen_spec {cfg : CFG χ η} {fuel : ℕ} {g g' : γ} {vc : β} {o : erased oracle}  :
  (@vcgen χ η β γ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ cfg fuel o).run g = (vc, g') →
  ∃ (vc_b : bool),
    sat g' vc (bv1 vc_b) ∧
    (vc_b = tt →
     bpf.cfg.safe_with_oracle cfg o.out) :=
begin
  intros mk,
  let init := ((initial_symstate cfg o).run g).1,
  let g' := ((initial_symstate cfg o).run g).2,
  have correct := symeval_correct cfg o.out fuel,
  obtain ⟨vc_b, sat₁, sound⟩ := @correct g' _ (_ : β) init tt tt _ true.intro _ _,
  { refine ⟨vc_b, ⟨sat₁, _⟩⟩,
    rintros ⟨⟩,
    obtain ⟨-, tail⟩ := sound rfl rfl,
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
