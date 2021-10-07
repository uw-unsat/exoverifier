/-
Copyright (c) 2021 The UNSAT Group. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luke Nelson, Xi Wang
-/
import .basic
import .cfg
import .decode
import misc.semidecision
import data.erased

namespace bpf

def trie_safe_with_regs (r : vector value nregs) (p : cfg.trie_program) : Prop :=
cfg.safe_with_regs p (bpf.reg.of_vector r)

def trie_safe (p : cfg.trie_program) : Prop :=
bpf.cfg.safe p

theorem trie_safe_of_erased_regs {p : cfg.trie_program} :
  (∀ (r : erased (vector value nregs)), trie_safe_with_regs r.out p) →
  trie_safe p :=
begin
  intros h,
  simp only [trie_safe, bpf.cfg.safe_iff_safe_with_all_regs],
  intros r,
  specialize h (erased.mk (bpf.reg.to_vector r)),
  simp only [erased.out_mk, trie_safe_with_regs, reg.to_of_vector] at h,
  exact h
end

def binary_safe_with_regs (r : vector value nregs) (b : list bool) : Prop :=
∃ (p : cfg.trie_program),
  (decode b).map cfg.trie_program.decode_from_flat = some p ∧
  cfg.safe_with_regs p (bpf.reg.of_vector r)

/-- Top-level specification of BPF program safety.
    A program is safe if and only if there exists a decoded CFG for that program
    and it is safe according to its operational semantics. -/
@[reducible]
def binary_safe (b : list bool) : Prop :=
∀ r, binary_safe_with_regs r b

theorem safe_of_erased_regs {b : list bool} :
  (∀ (r : erased (vector value nregs)), binary_safe_with_regs r.out b) →
  binary_safe b :=
begin
  intros h r,
  specialize h (erased.mk r),
  simp only [erased.out_mk] at h,
  exact h
end

end bpf
