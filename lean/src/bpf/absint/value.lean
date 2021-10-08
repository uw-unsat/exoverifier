/-
Copyright (c) 2021 The UNSAT Group. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luke Nelson, Xi Wang
-/
import data.domain.basic
import data.domain.bv
import bpf.basic

namespace absint

/--
Class for abstractions of values of BPF registers.
-/
class value_abstr (α : Type*) extends
  has_decidable_γ bpf.value α,
  abstr_le bpf.value α,
  abstr_top bpf.value α,
  abstr_join bpf.value α α,
  abstr_meet bpf.value α (with_bot α) :=

(doALU (op : bpf.ALU) :
  abstr_binary_transfer bpf.value α α (bpf.ALU.doALU op))

(doJMP_tt (op : bpf.JMP) :
  abstr_binary_inversion bpf.value α (with_bot α) (λ x y, op.doJMP x y = tt))

inductive avalue (β : Type) : Type
| scalar : β → avalue
| pointer : bpf.memregion → β → avalue

namespace avalue

variables {β : Type} [bv_abstr 64 β]

section has_to_pexpr
variable [has_to_pexpr β]

private meta def to_pexpr' : avalue β → pexpr
| (scalar x)  := ``(scalar %%x)
| (pointer m x) := ``(pointer %%m %%x)

meta instance : has_to_pexpr (avalue β) := ⟨to_pexpr'⟩

end has_to_pexpr

instance : has_γ bpf.value (avalue β) :=
sorry

instance : abstr_le bpf.value (avalue β) := sorry

instance : value_abstr (avalue β) :=
sorry

end avalue
end absint
