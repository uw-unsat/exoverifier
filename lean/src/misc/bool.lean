/-
Copyright (c) 2021 The UNSAT Group. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luke Nelson, Xi Wang
-/
import data.bool
import tactic.basic

theorem bool_iff_true {b : bool} : ↥b ↔ b = tt :=
by refl

/-- Boolean implication. -/
@[inline] def bimplies : bool → bool → bool
| ff _ := tt
| tt b := b

@[simp]
lemma bimplies_tt {b : bool} :
  bimplies b tt = tt :=
by cases b; refl

lemma bimplies_eq_bnot_bor (b₁ b₂ : bool) :
bimplies b₁ b₂ = !b₁ || b₂ :=
by cases b₁; cases b₂; refl

lemma bimplies_modus_ponens {b₁ b₂ : bool} :
bimplies b₁ b₂ → b₁ → b₂ :=
by cases b₁; cases b₂; tauto

/-- Boolean biconditional. -/
@[inline] def biff : bool → bool → bool
| tt tt := tt
| ff ff := tt
| _  _  := ff

@[simp]
lemma biff_tt (b : bool) : biff b tt = b :=
by cases b; refl

@[simp]
lemma biff_ff (b : bool) : biff b ff = !b :=
by cases b; refl

@[simp]
lemma tt_biff (b : bool) : biff tt b = b :=
by cases b; refl

@[simp]
lemma ff_biff (b : bool) : biff ff b = !b :=
by cases b; refl

@[simp]
lemma biff_self (b : bool) : biff b b = tt :=
by cases b; refl

@[simp]
lemma biff_eq_tt_iff_eq (b₁ b₂ : bool) : biff b₁ b₂ = tt ↔ b₁ = b₂ :=
by cases b₁; cases b₂; tauto

lemma biff_eq_bimplies_band_bimplies (b₁ b₂ : bool) :
biff b₁ b₂ = bimplies b₁ b₂ && bimplies b₂ b₁ :=
by cases b₁; cases b₂; refl

lemma biff_eq_bnot_bxor (b₁ b₂ : bool) :
biff b₁ b₂ = !bxor b₁ b₂ :=
by cases b₁; cases b₂; refl

lemma bxor_eq_bnot_biff (b₁ b₂ : bool) :
bxor b₁ b₂ = !biff b₁ b₂ :=
by cases b₁; cases b₂; refl

@[simp]
theorem biff_coe_iff (b₁ b₂ : bool) : biff b₁ b₂ ↔ (b₁ ↔ b₂) :=
by cases b₁; cases b₂; simp

@[simp]
theorem bxor_invol (b₁ b₂ : bool) : bxor b₁ (bxor b₁ b₂) = b₂ :=
by cases b₁; simp

theorem cond_eq_or_ands (b₁ b₂ b₃ : bool) :
  cond b₁ b₂ b₃ = (b₁ && b₂) || (!b₁ && b₃) :=
by cases b₁; simp

namespace bool

def full_add (a b cin : bool) : (bool × bool) :=
(bxor (bxor a b) cin, (a && b) || (cin && (a || b)))

end bool
