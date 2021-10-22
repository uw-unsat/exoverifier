/-
Copyright (c) 2021 The UNSAT Group. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luke Nelson, Xi Wang
-/
import .basic
import .bv
import data.bv.adc
import data.bv.basic
import misc.bool
import misc.vector

/-!
# Tristate numbers (tnum)

Each bit in a tnum can be either 0, 1, or "unknown".
-/

/-- Ternary digits. -/
@[reducible]
def trit := with_top (id bool)

namespace trit
open has_γ

private def and' : trit → trit → trit
| (some ff) _         := some ff
| _         (some ff) := some ff
| (some tt) (some tt) := some tt
| _          _        := none

protected def and : abstr_binary_transfer bool bool trit trit band :=
{ op      := and',
  correct := by {
    intros x y z u v h₁ h₂ _,
    subst_vars,
    cases x; cases y; cases u; cases v; cases h₁; cases h₂; dec_trivial } }

private def or' : trit → trit → trit
| (some tt) _         := some tt
| _         (some tt) := some tt
| (some ff) (some ff) := some ff
| _         _         := none

protected def or : abstr_binary_transfer bool bool trit trit bor :=
{ op      := or',
  correct := by {
    intros x y z u v h₁ h₂ _,
    subst_vars,
    cases x; cases y; cases u; cases v; cases h₁; cases h₂; dec_trivial } }

private def bimplies' : trit → trit → trit
| (some ff) _         := some tt
| _         (some tt) := some tt
| _         _         := none

protected def bimplies : abstr_binary_transfer bool bool trit trit bimplies :=
{ op      := bimplies',
  correct := by {
    intros x y z u v h₁ h₂ _,
    subst_vars,
    cases x; cases y; cases u; cases v; cases h₁; cases h₂; dec_trivial } }

protected def xor : abstr_binary_transfer bool bool trit trit bxor :=
with_top.lift_binary_relation $ id.binary_transfer bxor

protected def not : abstr_unary_transfer bool bool trit trit bnot :=
with_top.lift_unary_relation $ id.unary_transfer bnot

protected def full_add : Π (a b cin : trit), (trit × trit)
/- If all bits are known, result is known precisely. -/
| (some a) (some b) (some cin) :=
  let r := bool.full_add a b cin in (some r.1, some r.2)

/- If exactly one bit is unknown, `out` is unknown but carry can be known: if other inputs are both tt or ff. -/
| (some a) (some b) unknown   := (⊤, cond (biff a b) a ⊤)
| (some a) unknown (some cin) := (⊤, cond (biff a cin) a ⊤)
| unknown (some b) (some cin) := (⊤, cond (biff b cin) b ⊤)

/- If any two of the bits are unknown, the result is unknown. -/
| _ none none := ⊤
| none _ none := ⊤
| none none _ := ⊤

protected def full_add_correct {a b cin : trit} {a_b b_b cin_b : bool} :
  a_b ∈ γ a →
  b_b ∈ γ b →
  cin_b ∈ γ cin →
  bool.full_add a_b b_b cin_b ∈ γ (trit.full_add a b cin) :=
begin
  intros h₁ h₂ h₃,
  cases a; cases b; cases cin; simp only [trit.full_add];
    try{apply abstr_top.top_correct},
  { cases h_biff : (biff b cin),
    case ff { apply abstr_top.top_correct },
    simp only [biff_eq_tt_iff_eq] at h_biff,
    subst h_biff,
    cases h₂, cases h₃,
    simp only [bool.full_add, bxor_self, bool.bxor_ff_right, cond, bool.bxor_assoc],
    refine ⟨abstr_top.top_correct _, _⟩,
    cases a_b; cases b_b; dec_trivial },
  { cases h_biff : (biff a cin),
    case ff { apply abstr_top.top_correct },
    simp only [biff_eq_tt_iff_eq] at h_biff,
    subst h_biff,
    cases h₁, cases h₃,
    simp only [bool.full_add, cond, bool.bxor_assoc],
    refine ⟨abstr_top.top_correct _, _⟩,
    cases a_b; cases b_b; dec_trivial },
  { cases h_biff : (biff a b),
    case ff { apply abstr_top.top_correct },
    simp only [biff_eq_tt_iff_eq] at h_biff,
    subst h_biff,
    cases h₁, cases h₂,
    simp only [bool.full_add, cond, bool.bxor_assoc],
    refine ⟨abstr_top.top_correct _, _⟩,
    cases a_b; cases cin_b; dec_trivial },
  { cases h₁, cases h₂, cases h₃,
    split; refine rfl }
end

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

instance : has_γ (fin n → bool) (tnum n) :=
{ γ     := tnum.γ }

instance : has_decidable_γ (fin n → bool) (tnum n) :=
{ dec_γ := by {
    intros x y,
    apply @fintype.decidable_forall_fintype _ _ _,
    intros i,
    apply_instance } }

protected def const (v : fin n → bool) : abstr_nullary_relation (fin n → bool) (tnum n) (eq v) :=
{ op      := vector.of_fn $ λ i, (with_top.lift_nullary_relation (id.const (v i))).op,
  correct := by {
    intros _ h i,
    subst h,
    simp only [vector.nth_of_fn],
    apply (with_top.lift_nullary_relation _).correct rfl } }

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
        cases h₄ },
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

/-- Create the bitwise NOT of a tnums. -/
protected def not : tnum n → tnum n :=
vector.map trit.not.op

theorem not_correct ⦃x : fin n → bool⦄ ⦃a : tnum n⦄ :
  x ∈ γ a →
  bv.not x ∈ γ (tnum.not a) :=
begin
  intros h₁ i,
  simp only [tnum.not, vector.nth_map],
  apply trit.not.correct (h₁ i) rfl
end

section add

protected def adc : ∀ {n : ℕ}, tnum n → tnum n → trit → tnum n
| 0       _ _ carry := vector.nil
| (n + 1) a b carry :=
  let c  : (trit × trit) := trit.full_add a.head b.head carry,
      cs : tnum n        := @adc n a.tail b.tail c.2 in
    c.1 ::ᵥ cs

private theorem adc_correct {n : ℕ} {a b : tnum n} {c : trit} {x y : fin n → bool} {z : bool} :
  x ∈ γ a →
  y ∈ γ b →
  z ∈ γ c →
  bv.adc x y z ∈ γ (tnum.adc a b c) :=
begin
  induction n with n ih generalizing a b c x y z,
  case zero {
    intros _ _ _,
    refine fin.elim0 },
  case succ {
    intros h₁ h₂ h₃,
    specialize @ih a.tail b.tail (trit.full_add a.head b.head c).2 (fin.tail x) (fin.tail y) (bool.full_add (x 0) (y 0) z).2 _ _ _,
    { intros i,
      simp only [vector.nth_tail_succ],
      exact h₁ i.succ },
    { intros i,
      simp only [vector.nth_tail_succ],
      exact h₂ i.succ },
    { simp only [← vector.nth_zero],
      exact (trit.full_add_correct (h₁ 0) (h₂ 0) h₃).2 },
    simp only [tnum.adc],
    intros i,
    refine fin.cases _ _ i,
    { simp only [bv.adc_zero, vector.nth_cons_zero, ← vector.nth_zero],
      exact (trit.full_add_correct (h₁ 0) (h₂ 0) h₃).1 },
    { intros j,
      simp only [bv.adc_succ, vector.nth_cons_succ],
      exact ih j } }
end

protected def add (a b : tnum n) : tnum n :=
tnum.adc a b (some ff)

protected theorem add_correct ⦃x y : fin n → bool⦄ ⦃a b : tnum n⦄ :
  x ∈ γ a →
  y ∈ γ b →
  x + y ∈ γ (tnum.add a b) :=
begin
  intros h₁ h₂,
  simp only [bv.add_eq_adc],
  apply adc_correct h₁ h₂,
  dec_trivial
end

end add

protected def neg (a : tnum n) : tnum n :=
tnum.add (tnum.not a) (tnum.const 1).op

protected theorem neg_correct ⦃x : fin n → bool⦄ ⦃a : tnum n⦄ :
  x ∈ γ a →
  -x ∈ γ (tnum.neg a) :=
begin
  intros h₁,
  simp only [bv.neg_eq_not_add_one, tnum.neg],
  apply tnum.add_correct,
  { apply tnum.not_correct h₁ },
  { apply (tnum.const _).correct rfl }
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
protected def and : tnum n → tnum n → tnum n :=
vector.map₂ trit.and.op

protected theorem and_correct ⦃x y : fin n → bool⦄ ⦃a b : tnum n⦄ :
  x ∈ γ a →
  y ∈ γ b →
  bv.and x y ∈ γ (tnum.and a b) :=
begin
  intros h₁ h₂ i,
  simp only [tnum.and, vector.nth_map₂],
  apply trit.and.correct (h₁ i) (h₂ i) rfl
end

/-- Create the bitwise OR of two tnums. -/
protected def or : tnum n → tnum n → tnum n :=
vector.map₂ trit.or.op

protected theorem or_correct ⦃x y : fin n → bool⦄ ⦃a b : tnum n⦄ :
  x ∈ γ a →
  y ∈ γ b →
  bv.or x y ∈ γ (tnum.or a b) :=
begin
  intros h₁ h₂ i,
  simp only [tnum.or, vector.nth_map₂],
  apply trit.or.correct (h₁ i) (h₂ i) rfl
end

/-- Create the bitwise XOR of two tnums. -/
protected def xor : tnum n → tnum n → tnum n :=
vector.map₂ trit.xor.op

theorem xor_correct ⦃x y : fin n → bool⦄ ⦃a b : tnum n⦄ :
  x ∈ γ a →
  y ∈ γ b →
  bv.xor x y ∈ γ (tnum.xor a b) :=
begin
  intros h₁ h₂ i,
  simp only [tnum.xor, vector.nth_map₂],
  apply trit.xor.correct (h₁ i) (h₂ i) rfl
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
