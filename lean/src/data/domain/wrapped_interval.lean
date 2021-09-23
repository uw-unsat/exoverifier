/-
Copyright (c) 2021 The UNSAT Group. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luke Nelson, Xi Wang
-/
import .basic
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
    sorry },
  abstract         := const,
  abstract_correct := by apply const_correct }

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

protected def meet (a b : interval) : with_bot interval :=
sorry

theorem meet_correct ⦃a b : interval⦄ :
  γ a ∩ γ b ⊆ γ (wrapped_interval.meet a b) :=
begin
  sorry
end

instance : abstr_meet (fin n → bool) interval (with_bot interval) :=
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

instance : bv_abstr n (with_top interval) :=
{ add := with_top.lift_binary_transfer
   { op := wrapped_interval.add, correct := wrapped_interval.add_correct },
  and := with_top.lift_binary_transfer
   { op := wrapped_interval.and, correct := wrapped_interval.and_correct },
  or := with_top.lift_binary_transfer
   { op := wrapped_interval.or, correct := wrapped_interval.or_correct },
  xor := with_top.lift_binary_transfer
   { op := wrapped_interval.xor, correct := wrapped_interval.xor_correct },
  eq  := { inv := λ x y, (some x, some y), correct := by tauto } }

end
end wrapped_interval
