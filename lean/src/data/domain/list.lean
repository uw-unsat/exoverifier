/-
Copyright (c) 2021 The UNSAT Group. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luke Nelson, Xi Wang
-/
import .basic
import misc.list
import data.fin_enum

namespace list
variables {κ α β : Type*} [fin_enum κ] [has_γ α β] [inhabited β]
open has_γ

def interpret (t : list β) : κ → β :=
λ r, (t.nth ((fin_enum.equiv κ).to_fun r)).get_or_else (default _)

instance : has_γ (κ → α) (list β) :=
{ γ :=
    λ (t : list β) (f : κ → α), ∀ (k : κ), γ (interpret t k) (f k),
  abstract :=
    λ (f : κ → α), (fin_enum.to_list κ).map (λ k, abstract (f k)),
  abstract_correct := by {
    intros f k,
    simp only [interpret, list.nth_map, fin_enum.to_list, option.map_map, equiv.to_fun_as_coe],
    rw [list.nth_le_nth],
    { simp only [option.get_or_else_some, option.map_some', equiv.symm_apply_apply, function.comp_app, list.nth_le_fin_range, fin.eta],
      apply abstract_correct },
    { simp only [list.length_fin_range],
      apply fin.is_lt } } }

end list
