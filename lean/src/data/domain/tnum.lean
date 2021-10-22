/-
Copyright (c) 2021 The UNSAT Group. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luke Nelson, Xi Wang
-/
import .basic
import .bv
import data.bv.basic
import data.bv.circuit
import misc.bool
import misc.vector

/-!
# Tristate numbers (tnum)

Each bit in a tnum can be either 0, 1, or "unknown".
-/

/-- Ternary digits. -/
@[derive [decidable_eq, inhabited, has_reflect]]
inductive trit : Type
| one
| zero
| unknown

namespace trit

protected def γ : trit → set bool
| one     := eq tt
| zero    := eq ff
| unknown := λ _, true

local attribute [reducible] trit.γ

instance : has_decidable_γ bool trit :=
{ γ     := trit.γ,
  dec_γ := λ x y,
    match x with
    | one     := infer_instance
    | zero    := infer_instance
    | unknown := infer_instance
    end }

def const (x : bool) : abstr_nullary_relation bool trit (eq x) :=
{ op      := cond x one zero,
  correct := by {
    intros _ h,
    subst h,
    cases x; dec_trivial } }

protected def join : trit → trit → trit
| one  one  := one
| zero zero := zero
| _    _    := unknown

instance : abstr_join bool trit trit :=
{ join         := trit.join,
  join_correct := by {
    intros x y a h,
    cases x; cases y; cases h; cases h; dec_trivial } }

protected def meet : trit → trit → with_bot trit
| one     one     := some one
| zero    zero    := some zero
| a       unknown := some a
| unknown b       := some b
| _       _       := ⊥

instance : abstr_meet bool trit (with_bot trit) :=
{ meet         := trit.meet,
  meet_correct := by {
    intros x y a h,
    cases x; cases y; cases h with h₁ h₂; cases h₁; cases h₂; dec_trivial } }

protected def le : trit → trit → Prop
| one  one     := true
| zero zero    := true
| _    unknown := true
| _    _       := false

local attribute [reducible] trit.le

instance : abstr_le bool trit :=
{ le         := trit.le,
  dec_le := λ x y,
    match x, y with
    | zero,    zero    := infer_instance
    | zero,    one     := infer_instance
    | zero,    unknown := infer_instance
    | one,     zero    := infer_instance
    | one,     one     := infer_instance
    | one,     unknown := infer_instance
    | unknown, zero    := infer_instance
    | unknown, one     := infer_instance
    | unknown, unknown := infer_instance
    end,
  le_correct := by {
    intros x y h₁ _ h₂,
    cases x; cases y; cases h₁; cases h₂; dec_trivial } }

instance : abstr_top bool trit :=
{ top         := unknown,
  top_correct := by { intros, triv } }

end trit

/-- A tnum is a vector trits. -/
@[reducible]
def tnum (n : ℕ) := vector trit n

namespace tnum
variable {n : ℕ}
open has_γ

/-- Concretization function. Relates tnums to sets of bitvectors. -/
protected def γ (t : tnum n) : set (fin n → bool) :=
λ (v : fin n → bool), ∀ (i : fin n), v i ∈ γ (t.nth i)

local attribute [reducible] tnum.γ

instance : has_decidable_γ (fin n → bool) (tnum n) :=
{ γ     := tnum.γ,
  dec_γ := infer_instance }

protected def const (v : fin n → bool) : abstr_nullary_relation (fin n → bool) (tnum n) (eq v) :=
{ op      := vector.of_fn $ λ i, (trit.const (v i)).op,
  correct := by {
    intros _ h i,
    subst h,
    simp only [vector.nth_of_fn],
    apply (trit.const _).correct rfl } }

instance : abstr_top (fin n → bool) (tnum n) :=
{ top         := vector.repeat ⊤ n,
  top_correct := by {
    intros _ i,
    simp only [vector.nth_repeat] } }

protected def join : tnum n → tnum n → tnum n :=
vector.map₂ (⊔)

instance : abstr_join (fin n → bool) (tnum n) (tnum n) :=
{ join         := tnum.join,
  join_correct := by {
    intros x y u h i,
    cases h;
      simp only [tnum.join, vector.nth_map₂];
      apply abstr_join.join_correct,
    { left, exact h i },
    { right, exact h i } } }

protected def meet (x y : tnum n) : with_bot (tnum n) :=
let x : with_bot (flip vector n trit) := sequence (vector.map₂ abstr_meet.meet x y : flip vector n (with_bot trit)) in x

instance : abstr_meet (fin n → bool) (tnum n) (with_bot (tnum n)) :=
{ meet         := tnum.meet,
  meet_correct := by {
    induction n with n ih,
    { intros _ _ _ _,
      rw [vector.eq_nil x, vector.eq_nil y],
      refine fin.elim0 },
    { rintros x y u ⟨h₁, h₂⟩,
      rw [← vector.cons_head_tail x, ← vector.cons_head_tail y],
      simp only [tnum.meet, vector.map₂_cons],
      cases h₃ : (abstr_meet.meet (vector.head x) (vector.head y)),
      case none {
        have h₄ := abstr_meet.meet_correct ⟨h₁ 0, h₂ 0⟩,
        simp only [vector.nth_zero] at h₄,
        rw [h₃] at h₄,
        cases h₄,
        apply_instance },
      case some : tr {
        specialize @ih x.tail y.tail (fin.tail u) _,
        { split,
          { intros i,
            simp only [vector.nth_tail_succ],
            exact h₁ i.succ },
          { intros i,
            simp only [vector.nth_tail_succ],
            exact h₂ i.succ } },
        simp only [tnum.meet] at ih,
        simp only [sequence, traverse, option.map_some', id.def, option.map_eq_map, vector.traverse_def, has_seq.seq, option.some_bind'] at ⊢ ih,
        cases h₅ : vector.traverse id _,
        case none {
          rw [h₅] at ih,
          cases ih },
        case some {
          rw [h₅] at ih,
          simp only [option.map_some'],
          intros i,
          refine fin.cases _ _ i,
          { have h₆ := abstr_meet.meet_correct ⟨h₁ 0, h₂ 0⟩,
            simp only [vector.nth_zero] at h₆,
            rw [h₃] at h₆,
            simp only [vector.nth_cons_zero],
            exact h₆,
            exact (with_bot trit),
            apply_instance,
            apply_instance },
          { intros j,
            simp only [vector.nth_cons_succ],
            exact ih j } } } } } }

protected def le (a b : tnum n) : Prop :=
∀ (i : fin n), a.nth i ≤ b.nth i

instance : abstr_le (fin n → bool) (tnum n) :=
{ le     := tnum.le,
  dec_le := by {
    intros _ _,
    simp only [tnum.le],
    apply_instance },
  le_correct := by {
    intros x y l u h i,
    apply abstr_le.le_correct (l i) (h i) } }

protected def neg : tnum n → tnum n :=
⊤

protected theorem neg_correct ⦃x : fin n → bool⦄ ⦃a : tnum n⦄ :
  x ∈ γ a →
  -x ∈ γ (tnum.neg a) :=
begin
  intros _,
  apply @abstr_top.top_correct _ (tnum n) _
end

protected def add : tnum n → tnum n → tnum n :=
⊤

protected theorem add_correct ⦃x y : fin n → bool⦄ ⦃a b : tnum n⦄ :
  x ∈ γ a →
  y ∈ γ b →
  x + y ∈ γ (tnum.add a b) :=
begin
  intros h₁ h₂,
  simp only [tnum.add],
  apply abstr_top.top_correct _
end

protected def udiv : tnum n → tnum n → tnum n :=
⊤

protected theorem udiv_correct ⦃x y : fin n → bool⦄ ⦃a b : tnum n⦄ :
  x ∈ γ a →
  y ∈ γ b →
  x / y ∈ γ (tnum.udiv a b) :=
begin
  intros h₁ h₂,
  simp only [tnum.udiv],
  apply abstr_top.top_correct _
end

protected def urem : tnum n → tnum n → tnum n :=
⊤

protected theorem urem_correct ⦃x y : fin n → bool⦄ ⦃a b : tnum n⦄ :
  x ∈ γ a →
  y ∈ γ b →
  x % y ∈ γ (tnum.urem a b) :=
begin
  intros h₁ h₂,
  simp only [tnum.urem],
  apply abstr_top.top_correct _
end

protected def mul : tnum n → tnum n → tnum n :=
⊤

protected theorem mul_correct ⦃x y : fin n → bool⦄ ⦃a b : tnum n⦄ :
  x ∈ γ a →
  y ∈ γ b →
  x * y ∈ γ (tnum.mul a b) :=
begin
  intros h₁ h₂,
  simp only [tnum.mul],
  apply abstr_top.top_correct _
end

/-- Create the bitwise AND of two tnums. -/
protected def and (a b : tnum n) : tnum n :=
⊤

protected theorem and_correct ⦃x y : fin n → bool⦄ ⦃a b : tnum n⦄ :
  x ∈ γ a →
  y ∈ γ b →
  bv.and x y ∈ γ (tnum.and a b) :=
begin
  intros h₁ h₂,
  simp only [tnum.and],
  apply abstr_top.top_correct _
end

/-- Create the bitwise OR of two tnums. -/
protected def or (a b : tnum n) : tnum n :=
⊤

protected theorem or_correct ⦃x y : fin n → bool⦄ ⦃a b : tnum n⦄ :
  x ∈ γ a →
  y ∈ γ b →
  bv.or x y ∈ γ (tnum.or a b) :=
begin
  intros h₁ h₂,
  simp only [tnum.or],
  apply abstr_top.top_correct _
end

/-- Create the bitwise XOR of two tnums. -/
protected def xor (a b : tnum n) : tnum n :=
⊤

theorem xor_correct ⦃x y : fin n → bool⦄ ⦃a b : tnum n⦄ :
  x ∈ γ a →
  y ∈ γ b →
  bv.xor x y ∈ γ (tnum.xor a b) :=
begin
  intros h₁ h₂,
  simp only [tnum.xor],
  apply abstr_top.top_correct _
end

instance : bv_abstr n (tnum n) :=
{ const := tnum.const,
  neg  := { op := tnum.neg, correct := by { intros, subst_vars, apply tnum.neg_correct; assumption } },
  add  := { op := tnum.add, correct := by { intros, subst_vars, apply tnum.add_correct; assumption } },
  and  := { op := tnum.and, correct := by { intros, subst_vars, apply tnum.and_correct; assumption } },
  or   := { op := tnum.or, correct := by { intros, subst_vars, apply tnum.or_correct; assumption } },
  xor  := { op := tnum.xor, correct := by { intros, subst_vars, apply tnum.xor_correct; assumption } },
  udiv := { op := tnum.udiv, correct := by { intros, subst_vars, apply tnum.udiv_correct; assumption } },
  urem := { op := tnum.urem, correct := by { intros, subst_vars, apply tnum.urem_correct; assumption } },
  mul  := { op := tnum.mul, correct := by { intros, subst_vars, apply tnum.mul_correct; assumption } },
  shl  := { op := λ _ _, ⊤, correct := by { intros, subst_vars, apply @abstr_top.top_correct _ _ _ _ (bv.shl x y) } },
  lshr := { op := λ _ _, ⊤, correct := by { intros, subst_vars, apply @abstr_top.top_correct _ _ _ _ (bv.lshr x y) } },
  ashr := { op := λ _ _, ⊤, correct := by { intros, subst_vars, apply @abstr_top.top_correct _ _ _ _ (bv.ashr x y) } },
  lt   := abstr_binary_inversion.trivial,
  eq   := abstr_meet.invert_equality }

end tnum
