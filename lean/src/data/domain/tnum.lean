/-
Copyright (c) 2021 The UNSAT Group. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luke Nelson, Xi Wang
-/
import .basic
import .bv
import .trit
import smt.bitblast
import data.bv.adc
import data.bv.mul
import data.bv.sbc
import misc.bool
import misc.vector

/-!
# Tristate numbers (tnum)

A tristate number (tnum) overapproximates the set of values that a variable may take at the bit
level. Each bit of a variable may be either 0, 1, or unknown.

## Implementation notes

An earlier implementation represents each tnum as a pair of (value, mask), where the i-th bit of
the mask indicates whether the corresponding bit is known (0/1, as the i-th bit of the value) or
unknown. This is similar to the representation used by the Linux kernel. This complicates both
implementation and proof in Lean. We therefore switch to the current implementation.

## References

* Harishankar Vishwanathan, Matan Shachnai, Srinivas Narayana, and Santosh Nagarakatte.
  *Semantics, Verification, and Efficient Implementations for Tristate Numbers*.
  <https://arxiv.org/abs/2105.05398>
-/

/-- A tnum is a vector trits. -/
@[reducible]
def tnum (n : ℕ) := vector btrit n

namespace tnum
variable {n : ℕ}
open has_γ

private def repr' : Π {n : ℕ}, tnum n → string
| 0       _ := ""
| (n + 1) v :=
  let x := match v.head with
           | (some ff, _) := "0"
           | (some tt, _) := "1"
           | (none, _)    := "x"
           end in
    x ++ @repr' n v.tail

instance : has_repr (tnum n) := ⟨λ v, "0b" ++ repr' v.reverse⟩

/-- Concretization function. Relates tnums to sets of bitvectors. -/
protected def γ (t : tnum n) : set (fin n → bool) :=
λ (v : fin n → bool), smt.bitblast.eval unit.star t v

local attribute [reducible] tnum.γ

instance : has_γ (fin n → bool) (tnum n) :=
{ γ := tnum.γ }

-- instance : has_decidable_γ (fin n → bool) (tnum n) :=
-- { dec_γ := by {
--     intros x y,
--     apply @fintype.decidable_forall_fintype _ _ _,
--     intros i,
--     apply_instance } }

-- /-- Cast a constant to a tnum. -/
-- protected def const (v : fin n → bool) : abstr_nullary_relation (fin n → bool) (tnum n) (eq v) :=
-- { op      := vector.of_fn $ λ i, (with_top.lift_nullary_relation (id.const (v i))).op,
--   correct := by {
--     intros _ h i,
--     subst h,
--     simp only [vector.nth_of_fn],
--     apply (with_top.lift_nullary_relation _).correct rfl } }

-- instance : abstr_top (fin n → bool) (tnum n) :=
-- { top         := vector.repeat ⊤ n,
--   top_correct := by {
--     intros _ i,
--     simp only [vector.nth_repeat] } }

-- /-- Create the join of two tnums. -/
-- protected def join : tnum n → tnum n → tnum n :=
-- vector.map₂ (⊔)

-- instance : abstr_join (fin n → bool) (tnum n) (tnum n) :=
-- { join         := tnum.join,
--   join_correct := by {
--     intros x y u h i,
--     cases h;
--       simp only [tnum.join, vector.nth_map₂];
--       apply abstr_join.join_correct,
--     { left, exact h i },
--     { right, exact h i } } }

-- /-- Create the meet of two tnums. -/
-- protected def meet (x y : tnum n) : with_bot (tnum n) :=
-- let x : with_bot (flip vector n trit) := sequence (vector.map₂ abstr_meet.meet x y : flip vector n (with_bot trit)) in x

-- instance : abstr_meet (fin n → bool) (tnum n) (with_bot (tnum n)) :=
-- { meet         := tnum.meet,
--   meet_correct := by {
--     induction n with n ih,
--     { intros _ _ _ _,
--       rw [vector.eq_nil x, vector.eq_nil y],
--       refine fin.elim0 },
--     { rintros x y u ⟨h₁, h₂⟩,
--       rw [← vector.cons_head_tail x, ← vector.cons_head_tail y],
--       simp only [tnum.meet, vector.map₂_cons],
--       cases h₃ : (abstr_meet.meet (vector.head x) (vector.head y)),
--       case none {
--         have h₄ := abstr_meet.meet_correct ⟨h₁ 0, h₂ 0⟩,
--         simp only [vector.nth_zero] at h₄,
      --   rw [h₃] at h₄,
      --   cases h₄ },
      -- case some : tr {
      --   specialize @ih x.tail y.tail (fin.tail u) _,
      --   { split,
      --     { intros i,
      --       simp only [vector.nth_tail_succ],
      --       exact h₁ i.succ },
      --     { intros i,
      --       simp only [vector.nth_tail_succ],
      --       exact h₂ i.succ } },
      --   simp only [tnum.meet] at ih,
      --   simp only [sequence, traverse, option.map_some', id.def, option.map_eq_map, vector.traverse_def, has_seq.seq, option.some_bind'] at ⊢ ih,
      --   cases h₅ : vector.traverse id _,
      --   case none {
      --     rw [h₅] at ih,
      --     cases ih },
      --   case some {
      --     rw [h₅] at ih,
      --     simp only [option.map_some'],
      --     intros i,
      --     refine fin.cases _ _ i,
      --     { have h₆ := abstr_meet.meet_correct ⟨h₁ 0, h₂ 0⟩,
      --       simp only [vector.nth_zero] at h₆,
      --       rw [h₃] at h₆,
      --       simp only [vector.nth_cons_zero],
      --       exact h₆,
      --       exact (with_bot trit),
          --   apply_instance,
          --   apply_instance },
          -- { intros j,
          --   simp only [vector.nth_cons_succ],
          --   exact ih j } } } } } }

-- /-- Less-equal of two tnums is defined over each trit. -/
-- protected def le (a b : tnum n) : Prop :=
-- ∀ (i : fin n), a.nth i ≤ b.nth i

-- instance : abstr_le (fin n → bool) (tnum n) :=
-- { le     := tnum.le,
--   dec_le := by {
--     intros _ _,
--     simp only [tnum.le],
--     apply_instance },
--   le_correct := by {
--     intros x y l u h i,
--     apply abstr_le.le_correct (l i) (h i) } }

section and

def and {n : ℕ} (a b : tnum n) : tnum n :=
((smt.bitblast.mk_and a b).run unit.star).1

protected theorem and_correct ⦃x y : fin n → bool⦄ ⦃a b : tnum n⦄ :
  x ∈ γ a →
  y ∈ γ b →
  bv.and x y ∈ γ (tnum.and a b) :=
begin
  intros h₁ h₂,
  apply smt.bitblast.eval_mk_and (by rw [prod.mk.eta]) h₁ h₂,
end

end and

section xor

def xor {n : ℕ} (a b : tnum n) : tnum n :=
((smt.bitblast.mk_xor a b).run unit.star).1

protected theorem xor_correct ⦃x y : fin n → bool⦄ ⦃a b : tnum n⦄ :
  x ∈ γ a →
  y ∈ γ b →
  bv.xor x y ∈ γ (tnum.xor a b) :=
begin
  intros h₁ h₂,
  apply smt.bitblast.eval_mk_xor (by rw [prod.mk.eta]) h₁ h₂,
end

end xor

section add

/-- Create the addition of two tnums. -/
protected def add (a b : tnum n) : tnum n :=
((smt.bitblast.mk_add a b).run unit.star).1.1

protected theorem add_correct ⦃x y : fin n → bool⦄ ⦃a b : tnum n⦄ :
  x ∈ γ a →
  y ∈ γ b →
  x + y ∈ γ (tnum.add a b) :=
begin
  intros h₁ h₂,
  simp only [tnum.add],
  cases h : (smt.bitblast.mk_add a b).run () with fst,
  cases fst,
  exact (smt.bitblast.eval_mk_add h h₁ h₂).1
end

end add

section mul

/-- Create the multiplication of two tnums. -/
protected def mul (a b : tnum n) : tnum n :=
((smt.bitblast.mk_mul a b).run unit.star).1

protected theorem mul_correct ⦃x y : fin n → bool⦄ ⦃a b : tnum n⦄ :
  x ∈ γ a →
  y ∈ γ b →
  x * y ∈ γ (tnum.mul a b) :=
begin
  intros h₁ h₂,
  apply smt.bitblast.eval_mk_mul (by rw [prod.mk.eta]) h₁ h₂
end

end mul

section neg

/-- Create the negation of two tnums. -/
protected def neg (a : tnum n) : tnum n :=
sorry

protected theorem neg_correct ⦃x : fin n → bool⦄ ⦃a : tnum n⦄ :
  x ∈ γ a →
  -x ∈ γ (tnum.neg a) :=
begin
  sorry
end

end neg

section sub

/-- Create the subtraction of two tnums. -/
protected def sub (a b : tnum n) : tnum n :=
sorry

protected theorem sub_correct ⦃x y : fin n → bool⦄ ⦃a b : tnum n⦄ :
  x ∈ γ a →
  y ∈ γ b →
  x - y ∈ γ (tnum.sub a b) :=
begin
  sorry
end

end sub

section udiv

protected def udiv (a b : tnum n) : tnum n :=
((smt.bitblast.mk_udiv a b).run unit.star).1

protected theorem udiv_correct ⦃x y : fin n → bool⦄ ⦃a b : tnum n⦄ :
  x ∈ γ a →
  y ∈ γ b →
  x / y ∈ γ (tnum.udiv a b) :=
begin
  intros h₁ h₂,
  apply smt.bitblast.eval_mk_udiv (by rw [prod.mk.eta]) h₁ h₂
end

end udiv

section urem

protected def urem (a b : tnum n) : tnum n :=
((smt.bitblast.mk_urem a b).run unit.star).1

protected theorem urem_correct ⦃x y : fin n → bool⦄ ⦃a b : tnum n⦄ :
  x ∈ γ a →
  y ∈ γ b →
  x % y ∈ γ (tnum.urem a b) :=
begin
  intros h₁ h₂,
  apply smt.bitblast.eval_mk_urem (by rw [prod.mk.eta]) h₁ h₂
end

end urem

instance : bv_abstr n (tnum n) :=
{ const := sorry,
  neg  := sorry,
  not  := sorry,
  add  := { op := tnum.add, correct := by { intros, subst_vars, apply tnum.add_correct; assumption } },
  sub  := { op := tnum.sub, correct := by { intros, subst_vars, apply tnum.sub_correct; assumption } },
  and  := { op := tnum.and, correct := by { intros, subst_vars, apply tnum.and_correct; assumption } },
  or   := sorry,
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
