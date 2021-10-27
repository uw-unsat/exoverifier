/-
Copyright (c) 2021 The UNSAT Group. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luke Nelson, Xi Wang
-/
import .basic
import misc.bool

/-!
# Ternary digits / tri-state booleans

A trinary digit (trit) is an abstract domain for booleans with three values:
constant true and constant false, and an "unknown" value.
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

/-- Create the AND of two trits. -/
protected def and : abstr_binary_transfer band trit trit trit :=
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

/-- Create the OR of two trits. -/
protected def or : abstr_binary_transfer bor trit trit trit :=
{ op      := or',
  correct := by {
    intros x y z u v h₁ h₂ _,
    subst_vars,
    cases x; cases y; cases u; cases v; cases h₁; cases h₂; dec_trivial } }

private def bimplies' : trit → trit → trit
| (some ff) _         := some tt
| _         (some tt) := some tt
| (some tt) (some ff) := some ff
| _         _         := none

/-- Create the implication of two trits. -/
protected def bimplies : abstr_binary_transfer bimplies trit trit trit :=
{ op      := bimplies',
  correct := by {
    intros x y z u v h₁ h₂ _,
    subst_vars,
    cases x; cases y; cases u; cases v; cases h₁; cases h₂; dec_trivial } }

/-- Create the XOR of two trits. -/
protected def xor : abstr_binary_transfer bxor trit trit trit :=
with_top.lift_binary_relation $ id.binary_transfer bxor

/-- Create the NOT of two trits. -/
protected def not : abstr_unary_transfer bnot trit trit :=
with_top.lift_unary_relation $ id.unary_transfer bnot

/-- Create a full adder of two trits. -/
protected def full_add : Π (a b cin : trit), (trit × trit)
/- If all bits are known, result is known precisely. -/
| (some a) (some b) (some cin) :=
  let r := bool.full_add a b cin in (some r.1, some r.2)

/- If exactly one bit is unknown, `out` is unknown but carry can be known: if other inputs are both tt or ff. -/
| (some a) (some b) unknown    := (⊤, cond (biff a b) a ⊤)
| (some a) unknown  (some cin) := (⊤, cond (biff a cin) a ⊤)
| unknown  (some b) (some cin) := (⊤, cond (biff b cin) b ⊤)

/- If two or more inputs are unknown, all outputs are unknown. -/
| _ _ _ := ⊤

protected theorem full_add_correct {a b cin : trit} {a_b b_b cin_b : bool} :
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
