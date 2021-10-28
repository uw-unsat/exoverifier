/-
Copyright (c) 2021 The UNSAT Group. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luke Nelson, Xi Wang
-/
import .basic
import .bv
import data.bv.basic
import data.bv.circuit

/-!
# Wrapped-interval domain

## References
* <https://people.eng.unimelb.edu.au/schachte/papers/aplas12.pdf>
-/


structure interval (n : ℕ) [fact (n > 0)] :=
(first last : lsbvector n)
(wf         : first.nth ≠ last.nth + 1)

namespace interval
variables {n : ℕ} [fact (n > 0)]
open has_γ

protected def γ : interval n → set (fin n → bool)
| ⟨first, last, _⟩ :=
  if first.nth ≤ last.nth
  then { x | first.nth ≤ x ∧ x ≤ last.nth }
  else { x | x ≤ last.nth ∨ first.nth ≤ x }

instance : has_γ (fin n → bool) (interval n) :=
{ γ := interval.γ }

instance : has_decidable_γ (fin n → bool) (interval n) := sorry

protected def const (x : fin n → bool) : abstr_nullary_relation (= x) (interval n) :=
{ op := ⟨vector.of_fn x, vector.of_fn x, sorry⟩,
  correct := by {
    intros _ _,
    simp only [has_γ.γ, interval.γ],
    subst_vars,
    rw [if_pos],
    { simp only [vector.nth_of_fn_ext],
      split; refl },
    { refl } } }

def card : interval n → ℕ
| ⟨first, last, _⟩ := bv.to_nat (last.nth - first.nth + 1)

def compl : interval n → interval n
| ⟨first, last, h⟩ :=
  ⟨ bv.circuit.add last (vector.of_fn 1),
    bv.circuit.add first (vector.of_fn (bv.not 0)),
    by {
      simp only [bv.circuit.nth_add, vector.nth_of_fn_ext],
      contrapose! h,
      sorry } ⟩

protected def le (a b : interval n) : Prop :=
sorry

instance : abstr_le (fin n → bool) (interval n) :=
{ le         := interval.le,
  dec_le     := sorry,
  le_correct := sorry }

protected def join (a b : interval n) : with_top (interval n) :=
sorry

theorem join_correct ⦃a b : interval n⦄ :
  γ a ∪ γ b ⊆ γ (interval.join a b) :=
begin
  sorry
end

instance : abstr_join (fin n → bool) (interval n) (with_top (interval n)) :=
{ join := interval.join,
  join_correct := join_correct }

protected def meet (a b : with_top (interval n)) : with_bot (with_top (interval n)) :=
sorry

theorem meet_correct ⦃a b : with_top (interval n)⦄ :
  γ a ∩ γ b ⊆ γ (interval.meet a b) :=
begin
  sorry
end

instance : abstr_meet (fin n → bool) (with_top (interval n)) (with_bot (with_top (interval n))) :=
{ meet         := interval.meet,
  meet_correct := meet_correct }

protected def add (a b : interval n) : interval n :=
sorry

theorem add_correct ⦃x y : fin n → bool⦄ ⦃a b : interval n⦄ :
  x ∈ γ a →
  y ∈ γ b →
  x + y ∈ γ (interval.add a b) :=
begin
  sorry
end

protected def and (a b : interval n) : interval n :=
sorry

theorem and_correct ⦃x y : fin n → bool⦄ ⦃a b : interval n⦄ :
  x ∈ γ a →
  y ∈ γ b →
  bv.and x y ∈ γ (interval.and a b) :=
begin
  sorry
end

protected def or (a b : interval n) : interval n :=
sorry

theorem or_correct ⦃x y : fin n → bool⦄ ⦃a b : interval n⦄ :
  x ∈ γ a →
  y ∈ γ b →
  bv.or x y ∈ γ (interval.or a b) :=
begin
  sorry
end

protected def xor (a b : interval n) : interval n :=
sorry

theorem xor_correct ⦃x y : fin n → bool⦄ ⦃a b : interval n⦄ :
  x ∈ γ a →
  y ∈ γ b →
  bv.xor x y ∈ γ (interval.xor a b) :=
begin
  sorry
end

protected def udiv (a b : interval n) : interval n :=
sorry

theorem udiv_correct ⦃x y : fin n → bool⦄ ⦃a b : interval n⦄ :
  x ∈ γ a →
  y ∈ γ b →
  bv.udiv x y ∈ γ (interval.udiv a b) :=
begin
  sorry
end

protected def mul (a b : interval n) : interval n :=
sorry

theorem mul_correct ⦃x y : fin n → bool⦄ ⦃a b : interval n⦄ :
  x ∈ γ a →
  y ∈ γ b →
  bv.mul x y ∈ γ (interval.mul a b) :=
begin
  sorry
end

protected def urem (a b : interval n) : interval n :=
sorry

theorem urem_correct ⦃x y : fin n → bool⦄ ⦃a b : interval n⦄ :
  x ∈ γ a →
  y ∈ γ b →
  bv.urem x y ∈ γ (interval.urem a b) :=
begin
  sorry
end

protected def shl (a b : interval n) : interval n :=
sorry

theorem shl_correct ⦃x y : fin n → bool⦄ ⦃a b : interval n⦄ :
  x ∈ γ a →
  y ∈ γ b →
  bv.shl x y ∈ γ (interval.shl a b) :=
begin
  sorry
end

protected def lshr (a b : interval n) : interval n :=
sorry

theorem lshr_correct ⦃x y : fin n → bool⦄ ⦃a b : interval n⦄ :
  x ∈ γ a →
  y ∈ γ b →
  bv.lshr x y ∈ γ (interval.lshr a b) :=
begin
  sorry
end

protected def ashr (a b : interval n) : interval n :=
sorry

theorem ashr_correct ⦃x y : fin n → bool⦄ ⦃a b : interval n⦄ :
  x ∈ γ a →
  y ∈ γ b →
  bv.ashr x y ∈ γ (interval.ashr a b) :=
begin
  sorry
end

-- instance : abstr_bv (λ n, with_top (interval n)) :=
-- { neg := sorry,
--   const := λ x, with_top.lift_nullary_relation $ interval.const x,
--   not := sorry,
--   sub := sorry,
--   add := λ _, with_top.lift_binary_relation
--    { op := interval.add, correct := by { intros, subst_vars, apply interval.add_correct; assumption } },
--   and := with_top.lift_binary_relation
--    { op := interval.and, correct := by { intros, subst_vars, apply interval.and_correct; assumption } },
--   or := with_top.lift_binary_relation
--    { op := interval.or, correct := by { intros, subst_vars, apply interval.or_correct; assumption } },
--   xor := with_top.lift_binary_relation
--    { op := interval.xor, correct := by { intros, subst_vars, apply interval.xor_correct; assumption } },
--   udiv := with_top.lift_binary_relation
--    { op := interval.udiv, correct := by { intros, subst_vars, apply interval.udiv_correct; assumption } },
--   urem := with_top.lift_binary_relation
--    { op := interval.urem, correct := by { intros, subst_vars, apply interval.urem_correct; assumption } },
--   mul := with_top.lift_binary_relation
--    { op := interval.mul, correct := by { intros, subst_vars, apply interval.mul_correct; assumption } },
--   shl := with_top.lift_binary_relation
--    { op := interval.shl, correct := by { intros, subst_vars, apply interval.shl_correct; assumption } },
--   lshr := with_top.lift_binary_relation
--    { op := interval.lshr, correct := by { intros, subst_vars, apply interval.lshr_correct; assumption } },
--   ashr := with_top.lift_binary_relation
--    { op := interval.ashr, correct := by { intros, subst_vars, apply interval.ashr_correct; assumption } },
--   eq  := abstr_meet.invert_equality,
--   lt  := abstr_binary_inversion.trivial }

end interval
