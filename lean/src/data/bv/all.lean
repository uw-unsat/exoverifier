/-
Copyright (c) 2021 The UNSAT Group. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luke Nelson, Xi Wang
-/
import .basic
import misc.bool

namespace bv
variable {n : ℕ}

protected def all (v : fin n → bool) : bool :=
(list.of_fn v).all id

protected def any (v : fin n → bool) : bool :=
(list.of_fn v).any id

lemma all_iff (v : fin n → bool) :
  bv.all v ↔ ∀ i, v i :=
by simp [bv.all, list.all_iff_forall]

lemma all_biff_eq_to_bool_eq {n : ℕ} (b₁ b₂ : fin n → bool) :
  (bv.all (λ i, biff (b₁ i) (b₂ i))) = to_bool (b₁ = b₂) :=
begin
  rw [← bool.coe_bool_iff],
  simp only [bool.of_to_bool_iff],
  rw [bv.all_iff],
  split, swap,
  { intro h, subst h, simp },
  { intro h,
    funext i,
    specialize h i,
    cases (b₁ i); cases (b₂ i); tauto }
end

theorem any_eq_to_bool_nonzero {n : ℕ} (b₁ : fin n → bool) :
  bv.any b₁ = to_bool (b₁ ≠ 0) :=
begin
  rw [bv.any, ← bool.coe_bool_iff, list.any_iff_exists],
  simp only [bool.to_bool_not, exists_prop, id.def, exists_eq_right],
  split; intros h,
  { contrapose! h,
    simp only [bnot_eq_ff_eq_eq_tt, eq_ff_eq_not_eq_tt, to_bool_iff] at h,
    subst h,
    intro f,
    rw [list.mem_iff_nth] at f,
    simp only [list.nth_of_fn] at f,
    cases f with i f,
    simp only [has_zero.zero] at f,
    simp only [list.of_fn_nth_val] at f,
    split_ifs at f; tauto },
  { contrapose! h,
    simp only [bnot_eq_ff_eq_eq_tt, eq_ff_eq_not_eq_tt, to_bool_iff],
    rw [list.mem_iff_nth_le] at h,
    push_neg at h,
    funext i,
    specialize h i _,
    { rw [list.length_of_fn],
      cases i,
      tauto },
    simp only [eq_ff_eq_not_eq_tt, ne.def, list.nth_le_of_fn', fin.eta] at h,
    rw h,
    tauto }
end

end bv
