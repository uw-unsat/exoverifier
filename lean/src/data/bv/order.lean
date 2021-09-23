/-
Copyright (c) 2021 The UNSAT Group. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luke Nelson, Xi Wang
-/
import .basic

namespace bv

lemma eq_succ {n : ℕ} (v₁ v₂ : fin (n + 1) → bool) :
  v₁ = v₂ ↔
  (v₁ 0 = v₂ 0) ∧ (fin.tail v₁ = fin.tail v₂) :=
begin
  split; intro,
  { cc },
  { rw [← fin.cons_self_tail v₁, ← fin.cons_self_tail v₂],
    cc }
end

lemma ult_zero (v₁ v₂ : fin 0 → bool) :
  v₁ < v₂ ↔ false :=
begin
  simp only [has_lt.lt],
  simp [bv.ult]
end

lemma ult_succ {n : ℕ} (v₁ v₂ : fin (n + 1) → bool) :
  v₁ < v₂ ↔
  (fin.tail v₁ < fin.tail v₂) ∨ ((fin.tail v₁ = fin.tail v₂) ∧ (v₁ 0 = ff) ∧ (v₂ 0 = tt)) :=
begin
  simp only [has_lt.lt],
  simp only [bv.ult],
  conv_lhs { rw [← fin.cons_self_tail v₁, ← fin.cons_self_tail v₂] },
  simp only [to_nat_cons],
  cases v₁ 0; cases v₂ 0; simp [le_iff_lt_or_eq, to_nat_inj]
end

end bv
