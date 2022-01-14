/-
Copyright (c) 2021 The UNSAT Group. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luke Nelson, Xi Wang
-/
import data.bv.basic
import data.bv.vector
import data.counter
import data.erased
import data.option.order
import data.unordered_map.basic

/-!
# Satisfiability modulo theories

This file provides basic definitions for satisfiability modulo theories (SMT), in particular,
quantifier-free bit-vectors.

## Implementation notes

* Treat bools as bit-vectors with width one. This avoids type casts and simplifies formalization.

* Only core operators and their semantics are defined. Other operators such as `sub` are defined
  as functions.

## References

* <http://smtlib.cs.uiowa.edu/>
-/

universe u

namespace btor

/-- Core operators of nodes. -/
inductive node (α : Type u) : Type u
-- leaf
| var     : ∀ {n : ℕ}, erased (fin n → bool) → node
| const   : ∀ {n : ℕ}, lsbvector n → node
-- unary
| not     : α → node
-- bitwise
| and     : α → α → node
-- shift
| shl     : α → α → node
| lshr    : α → α → node
-- arithmetic
| add     : α → α → node
| mul     : α → α → node
| udiv    : α → α → node
| urem    : α → α → node
-- relational
| eq      : α → α → node
| ult     : α → α → node
-- concat/extract
| concat  : α → α → node
| extract : ℕ → ℕ → α → node
-- ternary
| ite     : α → α → α → node

@[reducible]
def graph (α : Type*) : Type* :=
α → option (node α)

namespace node
variables {α : Type u}

instance : inhabited (node α) :=
⟨node.var (default : (erased (fin 0 → bool)))⟩

/-- Evaluate a node according to its bitvector semantics. -/
@[mk_iff]
inductive sat (g : graph α) : α → (Σ n, fin n → bool) → Prop
| var : ∀ {a : α} {n : ℕ} {m : erased (fin n → bool)},
    g a = some (node.var m) →
    sat a ⟨n, m.out⟩
| const : ∀ {a : α} {n : ℕ} {m : lsbvector n},
    g a = some (node.const m) →
    sat a ⟨n, m.nth⟩
| not : ∀ {a a' : α} {n : ℕ} {v : fin n → bool},
    g a = some (node.not a') →
    sat a' ⟨n, v⟩ →
    sat a  ⟨n, bv.not v⟩
| and : ∀ {a a₁ a₂ : α} {n : ℕ} {v₁ v₂ : fin n → bool},
    g a = some (node.and a₁ a₂) →
    sat a₁ ⟨n, v₁⟩ →
    sat a₂ ⟨n, v₂⟩ →
    sat a  ⟨n, bv.and v₁ v₂⟩
| add : ∀ {a a₁ a₂ : α} {n : ℕ} {v₁ v₂ : fin n → bool},
    g a = some (node.add a₁ a₂) →
    sat a₁ ⟨n, v₁⟩ →
    sat a₂ ⟨n, v₂⟩ →
    sat a  ⟨n, v₁ + v₂⟩
| mul : ∀ {a a₁ a₂ : α} {n : ℕ} {v₁ v₂ : fin n → bool},
    g a = some (node.mul a₁ a₂) →
    sat a₁ ⟨n, v₁⟩ →
    sat a₂ ⟨n, v₂⟩ →
    sat a  ⟨n, v₁ * v₂⟩
| udiv : ∀ {a a₁ a₂ : α} {n : ℕ} {v₁ v₂ : fin n → bool},
    g a = some (node.udiv a₁ a₂) →
    sat a₁ ⟨n, v₁⟩ →
    sat a₂ ⟨n, v₂⟩ →
    sat a  ⟨n, v₁ / v₂⟩
| urem : ∀ {a a₁ a₂ : α} {n : ℕ} {v₁ v₂ : fin n → bool},
    g a = some (node.urem a₁ a₂) →
    sat a₁ ⟨n, v₁⟩ →
    sat a₂ ⟨n, v₂⟩ →
    sat a  ⟨n, v₁ % v₂⟩
| shl : ∀ {a a₁ a₂ : α} {n₁ n₂ : ℕ} {v₁ : fin n₁ → bool} {v₂ : fin n₂ → bool},
    g a = some (node.shl a₁ a₂) →
    sat a₁ ⟨n₁, v₁⟩ →
    sat a₂ ⟨n₂, v₂⟩ →
    sat a  ⟨n₁, bv.shl v₁ v₂⟩
| lshr : ∀ {a a₁ a₂ : α} {n₁ n₂ : ℕ} {v₁ : fin n₁ → bool} {v₂ : fin n₂ → bool},
    g a = some (node.lshr a₁ a₂) →
    sat a₁ ⟨n₁, v₁⟩ →
    sat a₂ ⟨n₂, v₂⟩ →
    sat a  ⟨n₁, bv.lshr v₁ v₂⟩
| eq : ∀ {a a₁ a₂ : α} {n : ℕ} {v₁ v₂ : fin n → bool},
    g a = some (node.eq a₁ a₂) →
    sat a₁ ⟨n, v₁⟩ →
    sat a₂ ⟨n, v₂⟩ →
    sat a  ⟨1, (λ _, v₁ = v₂)⟩
| ult : ∀ {a a₁ a₂ : α} {n : ℕ} {v₁ v₂ : fin n → bool},
    g a = some (node.ult a₁ a₂) →
    sat a₁ ⟨n, v₁⟩ →
    sat a₂ ⟨n, v₂⟩ →
    sat a  ⟨1, λ _, v₁ < v₂⟩
| concat : ∀ {a a₁ a₂ : α} {n₁ n₂ : ℕ} {v₁ : fin n₁ → bool} {v₂ : fin n₂ → bool},
    g a = some (node.concat a₁ a₂) →
    sat a₁ ⟨n₁, v₁⟩ →
    sat a₂ ⟨n₂, v₂⟩ →
    sat a  ⟨n₁ + n₂, bv.concat v₁ v₂⟩
| extract : ∀ {a a₁ : α} {upper lower n : ℕ} (h₁ : upper < n) (h₂ : lower ≤ upper) {v₁ : fin n → bool},
    g a = some (node.extract upper lower a₁) →
    sat a₁ ⟨n, v₁⟩ →
    sat a  ⟨upper - lower + 1, bv.extract upper lower h₁ h₂ v₁⟩
| ite : ∀ {a a₁ a₂ a₃ : α} {v₁ : fin 1 → bool} {n : ℕ} {v₂ v₃ : fin n → bool},
    g a = some (node.ite a₁ a₂ a₃) →
    sat a₁ ⟨1, v₁⟩ →
    sat a₂ ⟨n, v₂⟩ →
    sat a₃ ⟨n, v₃⟩ →
    sat a  ⟨n, bv.ite v₁ v₂ v₃⟩

/-- sat is preserved in bigger graphs. -/
theorem sat_of_subset {g g' : graph α} {x : α} {b : Σ n, fin n → bool} :
  sat g x b →
  g ≤ g' →
  sat g' x b :=
begin
  intros h l,
  induction h,
  case var : _ _ _ lookup {
    exact sat.var (l lookup) },
  case const : _ _ _ lookup {
    exact sat.const (l lookup) },
  case not : _ _ _ _ lookup sat₁ ih₁ {
    exact sat.not (l lookup) ih₁ },
  case and : _ _ _ _ _ _ lookup _ _ ih₁ ih₂ {
    exact sat.and (l lookup) ih₁ ih₂ },
  case shl : _ _ _ _ _ _ _ lookup _ _ ih₁ ih₂ {
    exact sat.shl (l lookup) ih₁ ih₂ },
  case lshr : _ _ _ _ _ _ _ lookup _ _ ih₁ ih₂ {
    exact sat.lshr (l lookup) ih₁ ih₂ },
  case eq : _ _ _ _ _ _ lookup _ _ ih₁ ih₂ {
    exact sat.eq (l lookup) ih₁ ih₂ },
  case add : _ _ _ _ _ _ lookup _ _ ih₁ ih₂ {
    exact sat.add (l lookup) ih₁ ih₂ },
  case mul : _ _ _ _ _ _ lookup _ _ ih₁ ih₂ {
    exact sat.mul (l lookup) ih₁ ih₂ },
  case udiv : _ _ _ _ _ _ lookup _ _ ih₁ ih₂ {
    exact sat.udiv (l lookup) ih₁ ih₂ },
  case urem : _ _ _ _ _ _ lookup _ _ ih₁ ih₂ {
    exact sat.urem (l lookup) ih₁ ih₂ },
  case ult : _ _ _ _ _ _ lookup _ _ ih₁ ih₂ {
    exact sat.ult (l lookup) ih₁ ih₂ },
  case concat : _ _ _ _ _ _ _ lookup _ _ ih₁ ih₂ {
    exact sat.concat (l lookup) ih₁ ih₂ },
  case extract :  _ _ _ _ _ h₁ h₂ _ lookup _ ih₁ {
    exact sat.extract h₁ h₂ (l lookup) ih₁ },
  case ite : _ _ _ _ _ _ _ _ lookup _ _ _ ih₁ ih₂ ih₃ {
    exact sat.ite (l lookup) ih₁ ih₂ ih₃ }
end

section insert
variables {σ : Type*} [unordered_map α (node α) σ] [counter α]
open unordered_map

/-- Lift an unordered map to a BTOR graph. -/
@[reducible]
def interpret (g : σ) : graph α :=
λ x, lookup x g

lemma subset_insert {g : σ} {id : α} {f : node α} :
  interpret g ≤ interpret (kinsert id f g) :=
begin
  intros i n h,
  rw [← option.mem_def, mem_lookup_iff] at ⊢ h,
  rw [mem_kinsert_iff],
  exact or.inl h
end

lemma interpret_insert {g : σ} {id : α} {f : node α} :
  id ∉ (to_list g).keys →
  interpret (kinsert id f g) id = some f :=
begin
  intro h,
  rw [← option.mem_def, unordered_map.mem_lookup_iff, mem_kinsert_iff],
  exact or.inr ⟨h, rfl⟩
end

end insert
end node

def ref (α : Type*) : Type* := α × Σ n, erased (fin n → bool)

namespace ref
variables {α : Type u}

@[reducible]
def id (r : ref α) : α := r.1

@[reducible]
def denotation (r : ref α) : erased Σ n, fin n → bool := r.2.2.bind (λ r', erased.mk ⟨r.2.1, r'⟩)

@[reducible]
def sat (g : graph α) (r : ref α) (e : Σ n, fin n → bool) : Prop := node.sat g r.id e ∧ e = r.denotation.out

end ref
end btor
