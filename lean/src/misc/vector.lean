/-
Copyright (c) 2021 The UNSAT Group. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luke Nelson, Xi Wang
-/
import data.vector
import data.vector.basic
import misc.reify
import tactic.linarith

/-!
# Miscellaneous vector functions and lemmas

The standard vector library is missing some functions and lemmas that are useful for us.
This file adds some micellaneous definitions to the vector namespace.
-/

namespace vector

section aux_defs

universe u

variables {α α₂ α₃ : Type*} {n : ℕ}

instance : inhabited (Σ (n : ℕ), vector α n) := ⟨⟨0, vector.nil⟩⟩

@[simp]
protected theorem traverse_nil {F : Type u → Type u} [applicative F] [is_lawful_applicative F] {α β : Type u} (f : α → F β) :
  vector.traverse f vector.nil = pure vector.nil := by refl

protected theorem map₂_to_list {x : vector α n} {y : vector α₂ n} {f : α → α₂ → α₃} :
  (map₂ f x y).to_list = (list.map₂ f x.to_list y.to_list) :=
by { cases x, cases y, refl }

/-- The `nth` value of map₂ is the function applied to the `nth` element of each vector. s-/
protected theorem nth_map₂ {x : vector α n} {y : vector α₂ n} {f : α → α₂ → α₃} {i : fin n} :
  (map₂ f x y).nth i = f (x.nth i) (y.nth i) :=
begin
  induction n generalizing x y i,
  { exact fin.elim0 i },
  { rw [vector.nth_eq_nth_le, ← vector.cons_head_tail x, ← vector.cons_head_tail y],
    simp_rw [vector.map₂_to_list, vector.to_list_cons, list.map₂],
    simp_rw [← vector.map₂_to_list],
    refine fin.cases _ _ i,
    { simp },
    { intros j,
      simp only [fin.val_eq_coe, cons_head_tail, fin.coe_succ, list.nth_le],
      simp_rw [← vector.nth_tail_succ, ← n_ih, vector.nth_eq_nth_le],
      refl } }
end

protected theorem map₂_cons {x : α} {xs : vector α n} {y : α₂} {ys : vector α₂ n} {f : α → α₂ → α₃} :
  (map₂ f (x ::ᵥ xs) (y ::ᵥ ys)) = (f x y) ::ᵥ map₂ f xs ys :=
begin
  ext i,
  simp only [vector.nth_map₂],
  refine fin.cases _ _ i,
  { simp },
  { simp only [nth_cons_succ, vector.nth_map₂],
    intro,
    refl }
end

/-- vector.cons behaves like a constructor. -/
protected theorem cons_inj {a : Type*} {x y : a} {n : ℕ} {xs ys : vector a n} :
  x ::ᵥ xs = y ::ᵥ ys ↔ x = y ∧ xs = ys :=
begin
  split, swap, cc,
  intros e,
  cases xs, cases ys,
  simp [vector.cons] at e,
  cc,
end

protected theorem cons_neq_iff {α : Type*} {n : ℕ} (x : α) (xs : vector α n) (v : vector α (n + 1)) :
  (x ::ᵥ xs ≠ v) ↔ (x ≠ v.head ∨ xs ≠ v.tail) :=
begin
  split; intros h,
  { contrapose! h,
    cases h with h₁ h₂; subst_vars,
    simp only [vector.cons_head_tail] },
  { contrapose! h,
    rw [← vector.cons_head_tail v, vector.cons_inj] at h,
    from h }
end

/--
  all_mem_iff_all_nth converts between proofs of all members of a vector, and proofs
  of vector.nth i for all indices i.
-/
lemma all_mem_iff_all_nth (v : vector α n) (p : α → Prop) :
  (∀ (x : α), x ∈ v.to_list → p x) ↔ (∀ (i : fin n), p (v.nth i)) :=
begin
  split; intros h,
  { intros i,
    apply h (v.nth i),
    apply vector.nth_mem },
  { intros x h,
    rw vector.mem_iff_nth at h,
    cases h with i h, subst h,
    apply h }
end

/-- Take all but the last element of a vector. -/
def init (v : vector α (n + 1)) : vector α n :=
  ⟨v.to_list.init, by {
    cases v with v h,
    rw list.length_init,
    simp only [to_list],
    rw h,
    simp }⟩

private lemma list_init_cons : ∀ (x : α) (xs : list α) (h : 0 < xs.length),
  (x :: xs).init = x :: xs.init
| a []        h := by cases h
| a (x :: xs) h := by { simp [list.init] }

private lemma list_init_nth_le : ∀ (l : list α) (n : ℕ) (h₁ : _) (h₂ : _),
  l.nth_le n h₁ = l.init.nth_le n h₂
| []        n h₁ _  := by cases h₁
| (x :: xs) n h₁ h₂ := by {
  simp only [nat.add_succ_sub_one, add_zero, list.length, list.length_init] at h₂,
  have : (x :: xs).init = x :: xs.init,
    apply list_init_cons,
    linarith,
  rw (list.nth_le_of_eq this),
  cases n,
  refl,
  simp only [list.nth_le],
  apply list_init_nth_le }

/-- The nth element v.init is the same as the nth element of v. -/
lemma nth_init : ∀ {n : ℕ} (v : vector α (n + 1)) (i : fin n), v.init.nth i = v.nth ↑i
| (n + 1) ⟨a::l, e⟩ ⟨i, h⟩ := by {
  simp [init, nth_eq_nth_le, list.init],
  rw ← list_init_nth_le }

lemma init_head : ∀ {n : ℕ} (v : vector α (n + 2)), v.init.head = v.head :=
begin
  intros _ _,
  rw [← vector.nth_zero, nth_init],
  simp
end

lemma tail_init_eq_init_tail : ∀ {n : ℕ} (v : vector α (n + 2)), v.init.tail = v.tail.init :=
begin
  intros _ _,
  apply vector.ext,
  intro i,
  repeat { rw [nth_init, nth_tail] },
  simp [fin.cast_succ_fin_succ]
end

lemma nth_cons_eq_cons_nth : ∀ {n : ℕ} {x : α} {xs : vector α n},
  (x ::ᵥ xs).nth = fin.cons x xs.nth :=
begin
  intros _ _ _,
  funext i,
  refine fin.cases _ _ i; by simp
end

lemma cons_nil_eq_iff_eq_head {v : vector α 1} {x : α} :
  (x ::ᵥ vector.nil) = v ↔ x = v.head :=
begin
  rw [← vector.cons_head_tail v],
  simp only [vector.singleton_tail, vector.cons_head],
  split,
  { intro h, injection h, cc },
  { intro h, subst h }
end

lemma init_singleton : ∀ (x : α), (x ::ᵥ vector.nil).init = vector.nil :=
begin
  intros _,
  apply vector.ext,
  intro i,
  rw [nth_init],
  simp only [nth_cons_nil],
  exact fin.elim0 i
end

lemma tail_nth_eq_nth_tail {n : ℕ} (v : vector α (n + 1)) :
  fin.tail v.nth = v.tail.nth :=
begin
  funext i,
  simp only [fin.tail, nth_tail_succ]
end

/-- Extensional version of `nth_of_fn`. -/
theorem nth_of_fn_ext (f : fin n → α) :
  (of_fn f).nth = f :=
begin
  funext i,
  simp,
end

end aux_defs

section last
variables {α : Type*} {n : ℕ}

theorem to_list_last (v : vector α (n + 1)) :
  v.to_list.last (list.ne_nil_of_length_pos (by simp)) = v.last :=
begin
  simp only [list.last_eq_nth_le],
  cases v with l h,
  simp [h, last, nth]
end

end last

section snoc
variables {α : Type*} {n : ℕ}

/-- Add an element at the end of a vector. -/
def snoc : vector α n → α → vector α (n + 1)
| ⟨l, h⟩ a := ⟨l ++ [a], by simpa⟩

theorem snoc_init_last (v : vector α (n + 1)) :
  snoc v.init v.last = v :=
begin
  rw ← to_list_last,
  simp [snoc, init, list.init_append_last]
end

theorem cons_snoc_eq_snoc_cons (a : α) (v : vector α n) (b : α) :
  a ::ᵥ (v.snoc b) = (a ::ᵥ v).snoc b :=
begin
  cases v,
  simp [cons, snoc]
end

theorem to_list_snoc {v : vector α n} {a : α} :
  (snoc v a).to_list = v.to_list ++ [a] :=
begin
  cases v,
  simp only [snoc],
  refl
end

end snoc

section reflect

/--
Convert a list to a vector n, doing something arbitrary when length of the list ≠ n.
Used to implement a `has_reflec` instance for vectors, which otherwise cannot be done
as they contain proof terms.
-/
private def list_to_vec {α : Type} [inhabited α] : list α → ∀ {n : ℕ}, vector α n
| _         0       := vector.nil
| (x :: xs) (n + 1) := vector.cons x $ list_to_vec xs
| []        n       := vector.repeat (default _) n

/-- Sanity check on `list_to_vec` that it sends `v.to_list` back to `v`. -/
private theorem list_to_vec_of_vec {α : Type} [inhabited α] {n : ℕ} (v : vector α n) :
  list_to_vec v.to_list = v :=
begin
  revert v,
  induction n; intros v,
  { rw [vector.eq_nil v],
    refl },
  { rw [← vector.cons_head_tail v, vector.to_list_cons, list_to_vec, n_ih] }
end

/-- Serialize vectors by converting to list and back. -/
instance (α : Type*) (α' : Type) [has_serialize α α'] [inhabited α'] (n : ℕ) :
  has_serialize (vector α n) (list α') :=
⟨ λ (v : vector α n), v.to_list.map has_serialize.serialize,
  λ (l : list α'), (list_to_vec l).map has_serialize.deserialize ⟩

meta instance (n : ℕ) : has_reflect (vector bool n)
| v :=
  let x : list bool := v.to_list,
      y : reflected_value (list bool) := reflected_value.mk x,
      z : reflected_value ℕ := reflected_value.mk n in
  unchecked_cast `(list_to_vec %%(y.expr) : vector bool %%(z.expr))

end reflect
end vector
