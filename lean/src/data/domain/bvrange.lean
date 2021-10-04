/-
Copyright (c) 2021 The UNSAT Group. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luke Nelson, Xi Wang
-/
import ...data.bv.basic
import .basic
import .bv
import algebra.field_power
import data.num.basic
import data.num.bitwise
import data.num.lemmas
import misc.vector
import order.bounded_lattice
import order.lattice
import tactic.linarith
import tactic.lint.frontend
import tactic.norm_num
import tactic.omega
import tactic.rcases
import tactic.ring

open has_γ

class bounded_linear_order (α : Type) extends linear_order α :=
(bot top : α)
(bot_le : ∀ (x : α), bot ≤ x)
(le_top : ∀ (x : α), x ≤ top)

namespace bvrange
section
parameters {n : ℕ} (ordering : bounded_linear_order (fin n → bool))

def lin : linear_order (fin n → bool) :=
@bounded_linear_order.to_linear_order _ ordering

abbreviation le : (fin n → bool) → (fin n → bool) → Prop :=
@linear_order.le _ lin

structure range :=
(lower upper : vector bool n)
(wf : le lower.nth upper.nth)

instance : has_decidable_γ (fin n → bool) range :=
{ γ := λ r x, (le r.lower.nth x) ∧ (le x r.upper.nth),
  dec_γ := by {
    intros x y,
    apply_instance },
  abstract := λ x,
    let b := vector.of_fn x in
     ⟨b, b, @linear_order.le_refl _ lin _⟩,
  abstract_correct := by {
    intros x,
    split,
    { simp [vector.nth_of_fn_ext],
      apply linear_order.le_refl _ },
    { simp [vector.nth_of_fn_ext],
      apply linear_order.le_refl _ } } }

def subrange (a b : range) : Prop :=
sorry

instance : decidable_rel subrange := sorry

instance : has_le range := ⟨subrange⟩

theorem subrange_correct (a b : range) :
  subrange a b → γ a ⊆ γ b :=
sorry

instance : abstr_le (fin n → bool) range :=
{ dec_le     := infer_instance,
  le_correct := subrange_correct }

def top : range :=
sorry

theorem top_correct (x : fin n → bool) :
  x ∈ γ top :=
sorry

instance : abstr_top (fin n → bool) range :=
{ top         := top,
  top_correct := top_correct }

def join (x y : range) : range :=
sorry

theorem join_correct (x y : range) :
  γ x ∪ γ y ⊆ γ (join x y) :=
sorry

instance : abstr_join (fin n → bool) range range :=
{ join         := join,
  join_correct := join_correct }

def meet (x y : range) : with_bot range :=
sorry

instance : abstr_meet (fin n → bool) range (with_bot range) :=
{ meet         := meet,
  meet_correct := sorry }

def add (x y : range) : range :=
sorry

theorem add_correct (x y : fin n → bool) (a b : range) :
  x ∈ γ a →
  y ∈ γ b →
  x + y ∈ γ (add a b) :=
sorry

instance : bv_abstr n range :=
{ add := { op := add, correct := add_correct },
  and := sorry,
  or  := sorry,
  xor := sorry,
  eq  := abstr_meet.invert_equality,
  lt  := abstr_binary_inversion.trivial }

end
end bvrange
