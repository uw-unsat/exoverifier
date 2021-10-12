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

def trie_safe_with_oracle (o : oracle) (p : cfg.trie_program) : Prop :=
cfg.safe_with_oracle p o

def trie_safe (p : cfg.trie_program) : Prop :=
bpf.cfg.safe p

theorem trie_safe_of_erased_regs {p : cfg.trie_program} :
  (∀ (o : erased oracle), trie_safe_with_oracle o.out p) →
  trie_safe p :=
begin
  intros h,
  intros o,
  specialize h (erased.mk o),
  simp only [erased.out_mk, trie_safe_with_oracle] at h,
  exact h
end

def binary_safe_with_oracle (o : oracle) (b : list bool) : Prop :=
∃ (p : cfg.trie_program),
  (decode b).map cfg.trie_program.decode_from_flat = some p ∧
  cfg.safe_with_oracle p o

/-- Top-level specification of BPF program safety.
    A program is safe if and only if there exists a decoded CFG for that program
    and it is safe according to its operational semantics. -/
@[reducible]
def binary_safe (b : list bool) : Prop :=
∀ o, binary_safe_with_oracle o b

theorem safe_of_erased_regs {b : list bool} :
  (∀ (o : erased oracle), binary_safe_with_oracle o.out b) →
  binary_safe b :=
begin
  intros h r,
  specialize h (erased.mk r),
  simp only [erased.out_mk] at h,
  exact h
end

end bpf
