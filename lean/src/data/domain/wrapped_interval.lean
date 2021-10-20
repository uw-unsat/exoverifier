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

namespace wrapped_interval
section
open has_γ

parameters {n : ℕ} (h : n > 0)

structure interval :=
(first last : lsbvector n)
(wf         : first.nth ≠ last.nth + 1)

protected def γ' : interval → set (fin n → bool)
| ⟨first, last, _⟩ :=
  if first.nth ≤ last.nth
  then { x | first.nth ≤ x ∧ x ≤ last.nth }
  else { x | x ≤ last.nth ∨ first.nth ≤ x }

def const (f : fin n → bool) : interval :=
⟨vector.of_fn f, vector.of_fn f,
  by {
    simp only [vector.nth_of_fn_ext],
    sorry } ⟩

theorem const_correct {f : fin n → bool} :
  f ∈ γ' (const f) :=
begin
  simp only [const, wrapped_interval.γ'],
  rw [if_pos],
  { simp only [vector.nth_of_fn_ext],
    split; refl },
  { refl }
end

instance : has_decidable_γ (fin n → bool) interval :=
{ γ                := wrapped_interval.γ',
  dec_γ            := by {
    rintros ⟨⟩,
    simp only [γ],
    intros x,
    sorry } }

def card : interval → ℕ
| ⟨first, last, _⟩ := bv.to_nat (last.nth - first.nth + 1)

def compl : interval → interval
| ⟨first, last, h⟩ :=
  ⟨ bv.circuit.add last (vector.of_fn 1),
    bv.circuit.add first (vector.of_fn (bv.not 0)),
    by {
      simp only [bv.circuit.nth_add, vector.nth_of_fn_ext],
      contrapose! h,
      sorry } ⟩

protected def le (a b : interval) : Prop :=
sorry

instance : has_le interval := ⟨wrapped_interval.le⟩

instance : decidable_rel le := sorry

theorem le_correct ⦃a b : interval⦄ :
  a ≤ b → γ a ⊆ γ b :=
sorry

instance : abstr_le (fin n → bool) interval :=
{ dec_le     := infer_instance,
  le_correct := le_correct }

protected def join (a b : interval) : with_top interval :=
sorry

theorem join_correct ⦃a b : interval⦄ :
  γ a ∪ γ b ⊆ γ (wrapped_interval.join a b) :=
begin
  sorry
end

instance : abstr_join (fin n → bool) interval (with_top interval) :=
{ join := join,
  join_correct := join_correct }

protected def meet (a b : with_top interval) : with_bot (with_top interval) :=
sorry

theorem meet_correct ⦃a b : with_top interval⦄ :
  γ a ∩ γ b ⊆ γ (wrapped_interval.meet a b) :=
begin
  sorry
end

instance : abstr_meet (fin n → bool) (with_top interval) (with_bot (with_top interval)) :=
{ meet := meet,
  meet_correct := meet_correct }

protected def add (a b : interval) : interval :=
sorry

theorem add_correct ⦃x y : fin n → bool⦄ ⦃a b : interval⦄ :
  x ∈ γ a →
  y ∈ γ b →
  x + y ∈ γ (wrapped_interval.add a b) :=
begin
  sorry
end

protected def and (a b : interval) : interval :=
sorry

theorem and_correct ⦃x y : fin n → bool⦄ ⦃a b : interval⦄ :
  x ∈ γ a →
  y ∈ γ b →
  bv.and x y ∈ γ (wrapped_interval.and a b) :=
begin
  sorry
end

protected def or (a b : interval) : interval :=
sorry

theorem or_correct ⦃x y : fin n → bool⦄ ⦃a b : interval⦄ :
  x ∈ γ a →
  y ∈ γ b →
  bv.or x y ∈ γ (wrapped_interval.or a b) :=
begin
  sorry
end

protected def xor (a b : interval) : interval :=
sorry

theorem xor_correct ⦃x y : fin n → bool⦄ ⦃a b : interval⦄ :
  x ∈ γ a →
  y ∈ γ b →
  bv.xor x y ∈ γ (wrapped_interval.xor a b) :=
begin
  sorry
end

protected def udiv (a b : interval) : interval :=
sorry

theorem udiv_correct ⦃x y : fin n → bool⦄ ⦃a b : interval⦄ :
  x ∈ γ a →
  y ∈ γ b →
  bv.udiv x y ∈ γ (wrapped_interval.udiv a b) :=
begin
  sorry
end

protected def mul (a b : interval) : interval :=
sorry

theorem mul_correct ⦃x y : fin n → bool⦄ ⦃a b : interval⦄ :
  x ∈ γ a →
  y ∈ γ b →
  bv.mul x y ∈ γ (wrapped_interval.mul a b) :=
begin
  sorry
end

protected def urem (a b : interval) : interval :=
sorry

theorem urem_correct ⦃x y : fin n → bool⦄ ⦃a b : interval⦄ :
  x ∈ γ a →
  y ∈ γ b →
  bv.urem x y ∈ γ (wrapped_interval.urem a b) :=
begin
  sorry
end

protected def shl (a b : interval) : interval :=
sorry

theorem shl_correct ⦃x y : fin n → bool⦄ ⦃a b : interval⦄ :
  x ∈ γ a →
  y ∈ γ b →
  bv.shl x y ∈ γ (wrapped_interval.shl a b) :=
begin
  sorry
end

protected def lshr (a b : interval) : interval :=
sorry

theorem lshr_correct ⦃x y : fin n → bool⦄ ⦃a b : interval⦄ :
  x ∈ γ a →
  y ∈ γ b →
  bv.lshr x y ∈ γ (wrapped_interval.lshr a b) :=
begin
  sorry
end

protected def ashr (a b : interval) : interval :=
sorry

theorem ashr_correct ⦃x y : fin n → bool⦄ ⦃a b : interval⦄ :
  x ∈ γ a →
  y ∈ γ b →
  bv.ashr x y ∈ γ (wrapped_interval.ashr a b) :=
begin
  sorry
end

instance : bv_abstr n (with_top interval) :=
{ neg := sorry,
  const := sorry,
  add := with_top.lift_binary_relation
   { op := wrapped_interval.add, correct := by { intros, subst_vars, apply wrapped_interval.add_correct; assumption } },
  and := with_top.lift_binary_relation
   { op := wrapped_interval.and, correct := by { intros, subst_vars, apply wrapped_interval.and_correct; assumption } },
  or := with_top.lift_binary_relation
   { op := wrapped_interval.or, correct := by { intros, subst_vars, apply wrapped_interval.or_correct; assumption } },
  xor := with_top.lift_binary_relation
   { op := wrapped_interval.xor, correct := by { intros, subst_vars, apply wrapped_interval.xor_correct; assumption } },
  udiv := with_top.lift_binary_relation
   { op := wrapped_interval.udiv, correct := by { intros, subst_vars, apply wrapped_interval.udiv_correct; assumption } },
  urem := with_top.lift_binary_relation
   { op := wrapped_interval.urem, correct := by { intros, subst_vars, apply wrapped_interval.urem_correct; assumption } },
  mul := with_top.lift_binary_relation
   { op := wrapped_interval.mul, correct := by { intros, subst_vars, apply wrapped_interval.mul_correct; assumption } },
  shl := with_top.lift_binary_relation
   { op := wrapped_interval.shl, correct := by { intros, subst_vars, apply wrapped_interval.shl_correct; assumption } },
  lshr := with_top.lift_binary_relation
   { op := wrapped_interval.lshr, correct := by { intros, subst_vars, apply wrapped_interval.lshr_correct; assumption } },
  ashr := with_top.lift_binary_relation
   { op := wrapped_interval.ashr, correct := by { intros, subst_vars, apply wrapped_interval.ashr_correct; assumption } },
  eq  := abstr_meet.invert_equality,
  lt  := abstr_binary_inversion.trivial }

end
end wrapped_interval
