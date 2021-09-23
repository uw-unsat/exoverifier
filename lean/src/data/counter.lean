/-
Copyright (c) 2021 The UNSAT Group. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luke Nelson, Xi Wang
-/
import data.num.lemmas
import tactic.omega.main

/--
Typeclass for homomorphism to natural numbers.

This is used for allocating sequential IDs, with the assumption of an initial element
and an increment operator.
-/
class counter (α : Type*) extends linear_order α :=
(to_nat : α → ℕ)
(init : α)
(next : α → α)
(next_to_nat : ∀ (x : α), to_nat (next x) = (to_nat x).succ)
(init_to_nat : to_nat init = 0)
(le_to_nat : ∀ (x y : α), x ≤ y ↔ to_nat x ≤ to_nat y)

namespace counter
variables {α : Type*} [counter α]

lemma to_nat_inj {x y : α} : to_nat x = to_nat y → x = y :=
begin
  intros h,
  have hl : to_nat x ≤ to_nat y, by rw h,
  have hr : to_nat y ≤ to_nat x, by rw h,
  rw ← le_to_nat at hl,
  rw ← le_to_nat at hr,
  apply le_antisymm; assumption
end

lemma lt_to_nat {x y : α} : x < y ↔ to_nat x < to_nat y :=
begin
  classical,
  by_cases (x = y); subst_vars,
  simp,
  have le2nat := counter.le_to_nat x y,
  simp [le_iff_lt_or_eq] at le2nat,
  have h₂ : ¬ (to_nat x = to_nat y), by {intro x, apply h, apply to_nat_inj x},
  rw [← eq_false] at h h₂,
  simp [h, h₂] at le2nat,
  from le2nat
end

lemma not_lt_init (x : α) : ¬(x < counter.init) :=
by simp [lt_to_nat, init_to_nat]

lemma lt_next (x : α) : x < next x :=
begin
  simp only [lt_to_nat, next_to_nat],
  generalize : (to_nat x) = y,
  change (y.succ) with (y + 1),
  simp only [nat.succ_pos', lt_add_iff_pos_right],
end

lemma lt_implies_lt_next {x y : α} :
  x < y → x < next y :=
begin
  rw [lt_to_nat],
  intro h,
  rw [lt_to_nat, next_to_nat, nat.succ_eq_add_one, nat.lt_add_one_iff, le_iff_lt_or_eq],
  left, assumption
end

lemma ne_implies_lt_add_one_iff_lt {x y : α} :
  x ≠ y →
  (x < next y ↔ x < y) :=
begin
  intro h,
  have hne : to_nat x ≠ to_nat y,
  { contrapose! h, apply to_nat_inj h },
  simp only [lt_to_nat, next_to_nat],
  omega
end

def of_nat : ℕ → α
| 0       := init
| (n + 1) := next (of_nat n)

lemma to_of_nat (x : ℕ) :
  to_nat (of_nat x : α) = x :=
begin
  induction x,
  { simp only [of_nat, init_to_nat] },
  { simp only [of_nat, next_to_nat, x_ih] }
end

lemma of_to_nat (x : α) :
  of_nat (to_nat x) = x :=
begin
  apply to_nat_inj,
  rw to_of_nat
end

lemma strong_induction_on
  {p : α → Prop} (n : α)
  (h : ∀ n, (∀ m, m < n → p m) → p n) : p n :=
begin
  revert h,
  rw [← of_to_nat n],
  generalize e : to_nat n = y,
  revert e n,
  induction y using nat.strong_induction_on with y ih,
  intros m h₁ h₂,
  apply h₂,
  simp only at ih,
  intros m l,
  specialize ih (to_nat m),
  rw [of_to_nat] at ih,
  apply ih,
  { rw [lt_to_nat, to_of_nat] at l,
    from l },
  { refl },
  { from h₂ }
end

end counter

instance : counter pos_num :=
⟨λ x, x.pred', pos_num.one, pos_num.succ,
  by simp [pos_num.pred'_to_nat, nat.succ_pred_eq_of_pos],
  by refl,
  by simp [pos_num.pred'_to_nat, nat.pred_le_iff, nat.succ_pred_eq_of_pos]⟩

instance : counter ℕ :=
⟨id, 0, nat.succ, by simp, by simp, by simp⟩

instance : counter num :=
⟨λ x, (x : ℕ), num.zero, num.succ, by simp [num.cast_succ], by simp, by simp⟩
