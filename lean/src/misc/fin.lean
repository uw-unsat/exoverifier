/-
Copyright (c) 2021 The UNSAT Group. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luke Nelson, Xi Wang
-/
import data.fin
import data.list
import misc.list
import tactic.omega.main

namespace fin
variables {n : ℕ} {α : Type*}

/-- Heterogeneous injectivity of list.of_fn. -/
theorem list_of_fn_inj_het {α : Type*} {n₁ n₂ : ℕ} {f₁ : fin n₁ → α} {f₂ : fin n₂ → α} :
  (list.of_fn f₁ = list.of_fn f₂) ↔ (n₁ = n₂ ∧ f₁ == f₂) :=
begin
  split; intros h,
  { have length_match := congr_arg list.length h,
    simp only [list.length_of_fn] at length_match,
    subst length_match,
    rw [heq_iff_eq],
    refine and.intro rfl _,
    ext ⟨i, _⟩,
    rw [← list.nth_le_of_fn f₁, ← list.nth_le_of_fn f₂],
    congr,
    from h },
  { cases h with h₁ h₂,
    subst h₁,
    rw [heq_iff_eq] at h₂,
    cases h₂,
    refl }
end

/-- Homogeneous injectivity of list.of_fn -/
theorem list_of_fn_inj (v₁ v₂ : fin n → α) : list.of_fn v₁ = list.of_fn v₂ ↔ v₁ = v₂ :=
by simp [list_of_fn_inj_het]

theorem list_of_fn_snoc {xs : fin n → α} {x : α} :
  list.of_fn (fin.snoc xs x : fin (n + 1) → α) = list.of_fn xs ++ [x] :=
begin
  ext i,
  simp only [list.nth_append_eq_ite, list.nth_of_fn, list.of_fn_nth_val, fin.snoc, list.length_of_fn, subtype.val],
  split_ifs,
  { simp },
  { simp only [option.mem_def, cast_eq],
    rw [list.nth_eq_some],
    simp only [exists_prop, list.length_singleton, list.nth_le_singleton],
    have : i - n < 1, by omega,
    rw [(iff_true _).2 this],
    simp },
  { exfalso,
    apply h,
    omega },
  { simp only [option.mem_def, cast_eq],
    simp only [false_iff],
    rw [list.nth_eq_some],
    push_neg,
    intros h,
    exfalso,
    change [x].length with 1 at h,
    apply h_1,
    omega }
end

theorem cast_eq_rec {β : Type*} (f : ∀ {n : ℕ}, (fin n → α) → β) {n' : ℕ} (h : n = n') (v : fin n → α) :
  f (@eq.rec_on _ _ _ _ h v) = f v :=
by subst h

section reverse

/-- Reverse a tuple. -/
def reverse (v : fin n → α) : fin n → α :=
λ ⟨i, h⟩, v ⟨n - i - 1, by omega⟩

def reverse_tail_eq_init_reverse (v : fin (n + 1) → α) :
  reverse (tail v) = init (reverse v) :=
begin
  ext ⟨_, _⟩,
  simp only [init, cast_succ_mk],
  simp only [reverse, tail, succ_mk],
  congr,
  omega
end

def reverse_last_eq_head (v : fin (n + 1) → α) :
  reverse v (fin.last n) = v 0 :=
begin
  simp only [fin.last],
  simp only [reverse],
  congr,
  omega
end

def reverse_reverse (v : fin n → α) :
  reverse (reverse v) = v :=
begin
  ext ⟨_, _⟩,
  simp only [reverse],
  congr,
  omega
end

theorem list_of_fn_reverse {f : fin n → α} :
  list.of_fn (fin.reverse f) = list.reverse (list.of_fn f) :=
begin
  ext i,
  simp only [option.mem_def, list.nth_of_fn, list.of_fn_nth_val],
  split_ifs,
  { have h' : i < (list.of_fn f).reverse.length, by simpa,
    rw [list.nth_le_nth h'],
    simp only [reverse],
    rw [list.nth_le_reverse'],
    { simp only [list.length_of_fn, list.nth_le_of_fn'],
      rw [← eq_iff_iff],
      congr' 3,
      omega },
    { simp only [list.length_of_fn, list.length_reverse] at h' ⊢,
      omega } },
  { simp only [false_iff],
    contrapose! h,
    rw [list.nth_eq_some] at h,
    cases h with h' _,
    simp only [list.length_of_fn, list.length_reverse] at h',
    from h' }
end

end reverse
end fin
