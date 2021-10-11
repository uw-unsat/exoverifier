/-
Copyright (c) 2021 The UNSAT Group. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luke Nelson, Xi Wang
-/
import .basic
import .cfg
import .spec
import .se.soundness
import aig.default
import misc.semidecision
import sat.default
import smt.bitblast.basic
import smt.bitblast.default

namespace bpf
namespace decision

section se

universes u
variables
  {η χ β γ : Type}
  [unordered_map η (bpf.cfg.instr η) χ] [decidable_eq η]
  [smt.factory β γ] [smt.extract_factory β γ] [smt.neg_factory β γ] [smt.add_factory β γ]
  [smt.and_factory β γ] [smt.const_factory β γ] [smt.eq_factory β γ] [smt.implies_factory β γ]
  [smt.redor_factory β γ] [smt.not_factory β γ] [smt.or_factory β γ] [smt.var_factory β γ]
  [smt.udiv_factory β γ] [smt.xor_factory β γ] [smt.sub_factory β γ] [smt.ult_factory β γ]
  [smt.mul_factory β γ] [smt.shl_factory β γ] [smt.lshr_factory β γ] [smt.ite_factory β γ]
  [smt.urem_factory β γ]
   {ω : Type} (smt_decider : smt.decision_procedure β γ ω) (smt_oracle : smt.oracle β γ ω)

include χ η β γ smt_decider
def decide_safe_with_regs_via_reduce_to_smt (fuel : ℕ) :
  semidecision.procedure (λ (e : (bpf.cfg.CFG χ η) × erased (vector value bpf.nregs)), bpf.cfg.safe_with_regs e.1 (bpf.reg.of_vector e.2.out)) ω :=
begin
  rintros ⟨p, regs⟩ w,
  rcases vch : (@cfg.se.vcgen χ η β γ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ p fuel regs).run (factory.init_f (Σ n, fin n → bool) β) with ⟨vc, g'⟩,
  refine (smt_decider (g', (vc, cfg.se.bv1 tt)) w).modus_ponens _,
  intros h,
  rcases cfg.se.vcgen_spec vch with ⟨b, sat₁, h'⟩,
  specialize h _ sat₁,
  rw [cfg.se.bv1_eq_iff] at h,
  subst h,
  exact h' rfl
end
omit smt_decider

meta def safe_with_regs_via_reduce_to_smt_oracle (fuel : ℕ) :
  semidecision.oracle (bpf.cfg.CFG χ η × erased (vector value bpf.nregs)) ω :=
λ ⟨p, r⟩,
  match (@cfg.se.vcgen χ η β γ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ p fuel r).run (factory.init_f (Σ n, fin n → bool) β) with
  | ⟨vc, g'⟩ := smt_oracle (g', (vc, ⟨1, λ _, tt⟩))
  end

include smt_decider
/-- Decide the safety of a binary BPF program by decoding the program and using se + smt.  -/
def decide_binary_safety_via_reduce_to_smt (fuel : ℕ) :
  semidecision.procedure
    (λ (e : erased (vector value nregs) × list bool), bpf.binary_safe_with_regs e.1.out e.2) ω :=
begin
  rintros ⟨r, b⟩ w,
  cases h : (decode b).map cfg.trie_program.decode_from_flat with p,
  { exact semidecision.unknown },
  { exact (decide_safe_with_regs_via_reduce_to_smt smt_decider fuel (p, r) w).modus_ponens (λ h₂, ⟨p, ⟨h, h₂⟩⟩) }
end
omit smt_decider

/-- Build a witness for the decision procedure of BPF safety. -/
meta def binary_safety_via_reduce_to_smt_oracle (fuel : ℕ) :
  semidecision.oracle (erased (vector value nregs) × list bool) ω :=
λ ⟨r, b⟩,
  match (decode b).map cfg.trie_program.decode_from_flat with
  | some p := safe_with_regs_via_reduce_to_smt_oracle smt_oracle fuel (p, r)
  | none   := tactic.fail "Failed to decode BPF program while generating proof."
  end

omit χ η β γ
namespace default

def decide_safe_with_regs_via_reduce_to_smt (fuel : ℕ) :
  semidecision.procedure (λ (e : bpf.cfg.trie_program × erased (vector value bpf.nregs)), bpf.cfg.safe_with_regs e.1 (bpf.reg.of_vector e.2.out)) sat.proof.default.proof :=
@bpf.decision.decide_safe_with_regs_via_reduce_to_smt
  pos_num _ (Σ n, vector aig.default.bref n) aig.default.factory _
  _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ sat.proof.default.proof
  (smt.bitblast.decide_via_reduce_to_sat aig.default.decide_via_to_cnf) fuel

/-- Default instances. -/
def decide_binary_safety_via_reduce_to_smt (fuel : ℕ) :
  semidecision.procedure (λ (e : erased (vector value nregs) × list bool), bpf.binary_safe_with_regs e.1.out e.2) sat.proof.default.proof :=
@bpf.decision.decide_binary_safety_via_reduce_to_smt
  pos_num (trie (bpf.cfg.instr pos_num)) (Σ n, vector aig.default.bref n) aig.default.factory _
  _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ sat.proof.default.proof
  (smt.bitblast.decide_via_reduce_to_sat aig.default.decide_via_to_cnf) fuel

/-- Build a witness for the decision procedure of BPF safety. -/
meta def binary_safety_via_reduce_to_smt_oracle (fuel : ℕ) :
  semidecision.oracle (erased (vector value nregs) × list bool) sat.proof.default.proof :=
@bpf.decision.binary_safety_via_reduce_to_smt_oracle pos_num (trie (bpf.cfg.instr pos_num)) (Σ n, vector aig.default.bref n) aig.default.factory _
  _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ sat.proof.default.proof (smt.bitblast.reduce_to_sat_oracle aig.to_cnf_oracle) fuel

end default

end se
end decision
end bpf
