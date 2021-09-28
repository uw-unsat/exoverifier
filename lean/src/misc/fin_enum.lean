/-
Copyright (c) 2021 The UNSAT Group. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luke Nelson, Xi Wang
-/
import data.fin
import data.fintype.basic
import data.fin_enum
import data.multiset.sort
import misc.list

namespace fin_enum
section to_vector
variables (α : Type*) [fin_enum α]

protected def to_vector : vector α (fin_enum.card α) :=
⟨ fin_enum.to_list α,
  by simp [to_list] ⟩

protected theorem nth_to_vector {x : α} :
  (fin_enum.to_vector α).nth ((fin_enum.equiv α).to_fun x) = x :=
begin
  simp only [fin_enum.to_vector, vector.nth, to_list, equiv.to_fun_as_coe, fin.val_eq_coe, equiv.symm_apply_apply,
             list.nth_le_fin_range, list.nth_le_map', fin.eta]
end

end to_vector
end fin_enum

namespace fin_enum
variables {α β : Type*} [fin_enum α] [inhabited β]

/--
Convert a function over a finite, enumerable type to a list.
-/
def fn_to_list (f : α → β) : list β :=
(fin_enum.to_list α).map f

/--
Convert a list to a function over a finite, enumerable type.
-/
def fn_of_list (l : list β) : α → β :=
λ x, (l.nth ((fin_enum.equiv α).to_fun x)).get_or_else (default _)

/--
Convert a function to expression by converting to list in meta-lean,
then converting out of list in regular lean.
-/
private meta def to_pexpr' [has_to_pexpr β] (f : α → β) : pexpr :=
``(fn_of_list %%(fn_to_list f))

meta instance [has_to_pexpr β] : has_to_pexpr (α → β) := ⟨to_pexpr'⟩

end fin_enum
