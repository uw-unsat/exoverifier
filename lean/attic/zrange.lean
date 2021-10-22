/-
Copyright (c) 2021 The UNSAT Group. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luke Nelson, Xi Wang
-/
import ...data.bv.basic
import .basic
import order.lattice
import order.bounded_lattice
import data.num.basic
import data.num.lemmas
import data.num.bitwise
import tactic.rcases
import tactic.norm_num
import tactic.omega
import tactic.ring
import tactic.linarith
import tactic.lint.frontend

/- range domain for bounded signed and unsigned arithmetic -/

namespace zrange

/-- Absolute bounds for ranges. For example, bounds of [0, 2^64) can be used to model
    ranges of (unsigned) 64-bit bitvectors. We use this in the type of `range` below
    as absolute bounds on the range of possible integers. -/
structure bounds : Type :=
(minimum maximum : znum)
(bounded         : minimum ≤ maximum)

instance : inhabited bounds := ⟨bounds.mk 0 0 (by dec_trivial)⟩

/-- Represents a contiguous range of integers that is a subset of [b.minimum, b.maximum]. -/
structure range (β : bounds) : Type :=
(lower upper : znum)
(valid       : lower ≤ upper)
(lowerBound  : β.minimum ≤ lower)
(upperBound  : upper ≤ β.maximum)

/-- A single integer in the range of [β.minimum, β.maximum]. We restrict ourselves to a
    subset of β since range operations do not make sense for values outside this region.
    (To see why, consider that if we used znum directly, then
    ¬∃ (⊤ : range β), ∀ (x : znum), x ∈ γ ⊤), i.e., there would be no top element.) -/
def bnum (β : bounds) : Type := { z : znum // β.minimum ≤ z ∧ z ≤ β.maximum }

namespace bnum
variable {β : bounds}

/--
Add two bnums, wrapping around from β.maximum to β.minimum on positive overflow
(and the reverse on negative overflow).
-/
def add (x y : bnum β) : bnum β :=
sorry

end bnum

section

variable {β : bounds}

/-- Relate a range over β to a set of bnums in β -/
def γ (p : range β) : set (bnum β) :=
λ (z : bnum β), p.lower ≤ z.1 ∧ z.1 ≤ p.upper

/-- znum.le is decidable, so γ is too. -/
instance : has_decidable_γ (bnum β) (range β) :=
{ γ                := γ,
  dec_γ            := by { dsimp only [decidable_pred, γ], apply_instance } }

/-- The range which is as big as the maximum bounds. -/
def top : range β :=
⟨β.minimum, β.maximum, β.bounded, le_refl _, le_refl _⟩

instance : inhabited (range β) := ⟨top⟩

lemma top_correct (b : bnum β) :
  b ∈ γ (top : range β) :=
begin
  dsimp only [γ, top],
  rcases b with ⟨_, _, _⟩,
  split; assumption,
end

instance : abstr_top (bnum β) (range β) :=
{ top         := top,
  top_correct := top_correct }

/-- Order ranges by inclusion. -/
@[reducible]
def le (r₁ r₂ : range β) : Prop :=
r₂.lower ≤ r₁.lower ∧ r₁.upper ≤ r₂.upper

/-- Union of two ranges. The union of two non-empty ranges must be non-empty, so no with_bot needed -/
def join (s t : range β) : range β :=
⟨ min s.lower t.lower, -- lower of two lower bounds
  max s.upper t.upper, -- higher of two upper bounds
  by {
    cases s, cases t,
    simp only [min_le_iff, le_max_iff],
    left, left, assumption },
  by {
    cases s, cases t,
    simp only [min, min_default],
    by_cases (s_lower ≤ t_lower),
    rw if_pos; assumption,
    rw if_neg; assumption },
  by {
    cases s, cases t,
    simp only [max, max_default],
    by_cases (t_upper ≤ s_upper),
    rw if_pos; assumption,
    rw if_neg; assumption } ⟩

/-- join behaves like set union. -/
lemma join_correct (a b : range β) :
  γ a ∪ γ b ⊆ γ (join a b) :=
begin
  cases a, cases b, dsimp only [join, γ],
  intros z h,
  simp only [set.mem_union_eq] at h,
  cases h; cases h with h1 h2; split;
    rw [min_le_iff] <|> rw [le_max_iff];
    try{left; assumption};
    right; assumption
end

instance : abstr_join (bnum β) (range β) (range β) :=
{ join         := join,
  join_correct := join_correct }

/-- Intersection of two ranges. Returns in with_bot because while ranges cannot be empty,
    the intersection of two ranges can be empty. -/
def meet (s t : range β) : with_bot (range β) :=
if H : s.upper < t.lower ∨ t.upper < s.lower
then ⊥
else
  some ⟨
    max s.lower t.lower, -- higher of two lower bounds
    min s.upper t.upper, -- lower of two upper bounds
    by {
      rw decidable.not_or_iff_and_not at H,
      cases H with h1 h2,
      simp only [not_lt] at h1, simp only [not_lt] at h2,
      cases s, cases t, dsimp only at *,
      cases (max_choice s_lower t_lower); rw h at *; clear h;
      cases (min_choice s_upper t_upper); rw h at *; clear h; assumption },
    by {
      cases s, cases t,
      cases (max_choice s_lower t_lower); rw h at *; assumption },
    by {
      cases s, cases t,
      cases (min_choice s_upper t_upper); rw h at *; assumption } ⟩

/-- meet behaves like set union. -/
lemma meet_correct (a b : range β) :
  γ a ∩ γ b ⊆ has_γ.γ (meet a b) :=
begin
  cases a, cases b,
  simp only [γ, meet],
  intros z h,
  simp only [set.mem_inter_eq] at h,
  rcases h with ⟨⟨h1, h2⟩, h3, h4⟩,
  split_ifs with f; dsimp only at f,
  { exfalso,
    rcases z with ⟨z, z_l, z_h⟩,
    cases f;
      rw ← znum.le_to_int at *;
      rw ← znum.lt_to_int at *;
    by omega },
  { rcases z with ⟨z, z_l, z_h⟩,
    simp only [has_γ.γ, with_bot.has_γ._match_1, γ],
    split,
    { rw [max_le_iff], split; assumption },
    { rw [le_min_iff], split; assumption } }
end

instance : abstr_meet (bnum β) (range β) (with_bot $ range β) :=
{ meet         := meet,
  meet_correct := meet_correct }

/-- Approximation of integer addition of two ranges. -/
def add (s t : range β) : range β :=
if oflow : (s.upper + t.upper > β.maximum) ∨ (s.lower + t.lower < β.minimum)
then top
else
  ⟨ s.lower + t.lower, -- add lower ranges
    s.upper + t.upper, -- add upper ranges
    by {
      push_neg at oflow,
      cases oflow with h1 h2,
      cases s, cases t,
      dsimp only at *,
      repeat {rw ← znum.le_to_int at * <|> rw znum.cast_add at *},
      omega },
    by {
      push_neg at oflow,
      cases oflow with h1 h2,
      cases s, cases t,
      dsimp only at *,
      repeat {rw ← znum.le_to_int at * <|> rw znum.cast_add at *},
      omega },
    by {
      push_neg at oflow,
      cases oflow with h1 h2,
      cases s, cases t,
      dsimp only at *,
      repeat {rw ← znum.le_to_int at * <|> rw znum.cast_add at *},
      omega } ⟩

theorem add_correct {x y : bnum β} {a b : range β} :
  x ∈ γ a →
  y ∈ γ b →
  bnum.add x y ∈ γ (add a b) :=
sorry

end -- section
end zrange
