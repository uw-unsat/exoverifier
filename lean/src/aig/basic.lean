/-
Copyright (c) 2021 The UNSAT Group. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luke Nelson, Xi Wang
-/
import data.counter
import data.erased
import data.hashable
import data.option.order
import data.trie.trien
import data.unordered_map.basic
import data.unordered_map.trie
import misc.bool

/-!
# And-inverter graphs

This file provides support for and-inverter graphs (AIGs).

An AIG is a directed acyclic graph. Each node takes either zero (variable) or two inputs (AND).
Each edge may be inverted, enabling compact representation of logical operators.

## Implementation notes

* The representation is split into two parts: (unnamed) `ref` represents top-level inversion or
  constants, while (named) `node` represents internal nodes. In other words, it maintains that
  there are no constants as internal nodes.

* An earlier implementation defines AIG nodes as inductive data types (circuits) with IDs. While
  doing so simplifies the semantics and the correctness proof for AIG-to-CNF translation, it
  complicates the upper layers and leads to repeated reasoning of membership, especially with more
  AIG optimizations.

  inductive node (α : Type*)
  | var : α → bool → node
  | and : α → node → bool → node → bool → node

## References

* Robert Brummayer. *C32SAT: A Satisfiable Checker for C Expressions*.
  <http://fmv.jku.at/papers/Brummayer-MasterThesis06.pdf>
-/

namespace aig

/-- An AIG node is either a variable or a logical conjunction. -/
@[derive decidable_eq]
inductive node (α : Type*)
| var : erased bool → node
| and : α → bool → α → bool → node

/-- An AIG graph is a partial function from node identifiers to nodes. -/
@[reducible]
def graph (α : Type*) : Type* :=
α → option (node α)

namespace node
variables {α : Type*}

instance : inhabited (node α) :=
⟨node.var $ default⟩

section repr
variable [has_repr α]

private def repr : node α → string
| (var b)           := "(var " ++ has_repr.repr b ++ ")"
| (and a₁ b₁ a₂ b₂) := "(and " ++ cond b₁ "-" "" ++ has_repr.repr a₁ ++ " " ++
                                  cond b₂ "-" "" ++ has_repr.repr a₂ ++ ")"

instance : has_repr (node α) :=
⟨repr⟩

end repr

/-- Relate a node in an AIG to a bool it interprets to. -/
@[mk_iff]
inductive sat (g : graph α) : α → bool → Prop
| var :
  ∀ {b : erased bool} {id : α},
    g id = some (node.var b) →
    sat id b.out
| and :
  ∀ {b₁ b₂ r₁ r₂ : bool} {id n₁ n₂ : α},
    g id = some (node.and n₁ b₁ n₂ b₂) →
    sat n₁ r₁ →
    sat n₂ r₂ →
    sat id ((bxor b₁ r₁) && (bxor b₂ r₂))

/-- Two sat derivations of the same AIG and node always agree on the interpretation. -/
theorem sat_inj {g : graph α} {x : α} {b₁ : bool} :
  sat g x b₁ →
  ∀ {b₂ : bool},
    sat g x b₂ →
    b₁ = b₂ :=
begin
  intro h₁,
  induction h₁,
  case var { intros _ h₂; cases h₂; cc },
  case and : _ _ _ _ _ _ _ lookup₁ sat₁₁ sat₁₂ ih₁₁ ih₁₂ {
    intros b₂ h₂,
    cases h₂,
    case var { cc },
    case and : _ _ _ _ _ _ _ lookup₂ sat₂₁ sat₂₂ {
      rw lookup₁ at lookup₂,
      cases lookup₂,
      specialize ih₁₁ sat₂₁,
      specialize ih₁₂ sat₂₂,
      subst_vars } }
end

def sat_right_unique (g : graph α) : relator.right_unique (sat g) :=
λ _ _ _ h, sat_inj h

/-- sat is preserved in bigger graphs. -/
theorem sat_of_subset {g g' : graph α} {x : α} {b : bool} :
  sat g x b →
  g ≤ g' →
  sat g' x b :=
begin
  intros h l,
  induction h,
  case var : _ _ lookup {
    exact sat.var (l lookup) },
  case and : _ _ _ _ _ _ _ lookup _ _ ih₁ ih₂ {
    exact sat.and (l lookup) ih₁ ih₂ }
end

protected lemma bxor_eq_tt_iff {b₁ b₂ : bool} :
  bxor b₁ b₂ = tt ↔ !b₁ = b₂ :=
by cases b₁; cases b₂; tauto

protected lemma bxor_eq_ff_iff {b₁ b₂ : bool} :
  bxor b₁ b₂ = ff ↔ b₁ = b₂ :=
by cases b₁; cases b₂; tauto

theorem sat_and_iff {g : graph α} {n_id : α} {n₁ : α} {b₁ : bool} {n₂ : α} {b₂ : bool} {r₃ : bool} :
  g n_id = some (node.and n₁ b₁ n₂ b₂) →
  (node.sat g n_id r₃ ↔ (∃ r₁ r₂, node.sat g n₁ r₁ ∧ node.sat g n₂ r₂ ∧ r₃ = bxor b₁ r₁ && bxor b₂ r₂)) :=
begin
  intros lookup,
  rw [sat_iff],
  simp only [lookup, false_or],
  split,
  { simp only [false_and, exists_false, false_or],
     rintros ⟨_, _, _, _, _, _, ⟨⟨⟩, ⟨⟩, ⟨⟩, ⟨⟩⟩, _, _, ⟨⟩⟩,
    tauto },
  { tauto }
end

theorem sat_and_tt_iff {g : graph α} {n_id : α} (n₁ : α) (b₁ : bool) (n₂ : α) (b₂ : bool) :
  g n_id = some (node.and n₁ b₁ n₂ b₂) →
  (node.sat g n_id tt ↔ node.sat g n₁ (!b₁) ∧ node.sat g n₂ (!b₂)) :=
begin
  intros lookup,
  rw [sat_and_iff lookup],
  split,
  { rintros ⟨_, _, _, _, h⟩,
    symmetry' at h,
    simp only [band_eq_true_eq_eq_tt_and_eq_tt] at h,
    cases h with h₁ h₂,
    rw [node.bxor_eq_tt_iff] at h₁ h₂,
    subst h₁, subst h₂,
    tauto },
  { rintros ⟨h₁, h₂⟩,
    existsi [!b₁, !b₂],
    refine ⟨h₁, ⟨h₂, _⟩⟩,
    simp }
end

section insert
variables {σ : Type*} [unordered_map α (node α) σ] [counter α]
open unordered_map

/-- Lift an unordered map to an AIG graph. -/
@[reducible]
def interpret (g : σ) : graph α :=
λ x, lookup x g

/-- Insert a new `var` node into the map. -/
def insert_var (g : σ) (id : α) (b : erased bool) : σ :=
kinsert id (node.var b) g

lemma subset_insert_var {g : σ} {id : α} {b : erased bool} :
  interpret g ≤ interpret (insert_var g id b) :=
begin
  intros i n h,
  simp only [insert_var, ← option.mem_def, mem_lookup_iff, mem_kinsert_iff] at h ⊢,
  exact or.inl h
end

lemma sat_insert_var {g : σ} {id : α} {b : erased bool} :
  id ∉ (unordered_map.to_list g).keys →
  sat (interpret (insert_var g id b)) id b.out :=
begin
  intro notin,
  apply sat.var,
  simp only [insert_var, ← option.mem_def, mem_lookup_iff, mem_kinsert_iff],
  right,
  tauto
end

/-- Insert a new `and` node into the map. -/
def insert_and (g : σ) (id : α) (n₁ : α) (b₁ : bool) (n₂ : α) (b₂ : bool) : σ :=
unordered_map.kinsert id (node.and n₁ b₁ n₂ b₂) g

lemma subset_insert_and {g : σ} {id n₁ n₂ : α} {b₁ b₂ : bool} :
  interpret g ≤ interpret (insert_and g id n₁ b₁ n₂ b₂) :=
begin
  intros i n h,
  simp only [insert_and, ← option.mem_def, mem_lookup_iff, mem_kinsert_iff] at ⊢ h,
  exact or.inl h
end

lemma sat_insert_and {g : σ} {id n₁ n₂ : α} {b₁ b₂ r₁ r₂ : bool} :
  id ∉ (unordered_map.to_list g).keys →
  sat (interpret g) n₁ r₁ →
  sat (interpret g) n₂ r₂ →
  sat (interpret (insert_and g id n₁ b₁ n₂ b₂)) id ((bxor b₁ r₁) && (bxor b₂ r₂)) :=
begin
  intros notin sat_n₁ sat_n₂,
  apply sat.and,
  { rw [← option.mem_def, unordered_map.mem_lookup_iff, insert_and, unordered_map.mem_kinsert_iff],
    right, tauto },
  { apply sat_of_subset sat_n₁,
    apply subset_insert_and },
  { apply sat_of_subset sat_n₂,
    apply subset_insert_and }
end

end insert
end node

/-- A reference of an AIG node, modeling the top-level edge.

Internal edges are modeled by AND gates in `node`.
-/
@[derive [decidable_eq, has_reflect]]
inductive ref (α : Type*)
| top  : ref
| bot  : ref
| root : α → bool → ref

/-- `ref` with a concrete interpretation. -/
abbreviation bref (α : Type*) : Type* := ref α × erased bool

namespace ref
variables {α : Type*}

instance : inhabited (ref α) :=
⟨top⟩

section repr
variable [has_repr α]

private def repr : ref α → string
| top        := "⊤"
| bot        := "⊥"
| (root a b) := cond b "-" "" ++ has_repr.repr a

instance : has_repr (ref α) :=
⟨repr⟩

end repr

/-- Make a reference to a node with a regular edge. -/
@[reducible]
def mk_reg (a : α) : ref α :=
ref.root a ff

/-- Make a reference to a node with an inverted edge. -/
@[reducible]
def mk_inv (a : α) : ref α :=
ref.root a tt

/-- Evaluate a `ref` to bool. -/
@[mk_iff]
inductive sat (g : graph α) : ref α → bool → Prop
| top  : sat top tt
| bot  : sat bot ff
| root : ∀ {a : α} {b r : bool},
  node.sat g a r →
  sat (root a b) (bxor b r)

lemma sat_top_iff {g : graph α} {b : bool} :
  sat g top b ↔ b = tt :=
begin
  split; rintro ⟨⟩,
  { refl },
  { constructor }
end

lemma sat_bot_iff {g : graph α} {b : bool} :
  sat g bot b ↔ b = ff :=
begin
  split; rintro ⟨⟩,
  { refl },
  { constructor }
end

lemma sat_root_iff {g : graph α} {a : α} {b r : bool} :
  sat g (root a b) r ↔ node.sat g a (bxor b r) :=
begin
  split; intro h,
  { cases h,
    simpa only [bxor_invol] },
  { have : r = (bxor b (bxor b r)), by simp,
    rw this,
    constructor,
    exact h }
end

theorem sat_inj {g : graph α} {x : ref α} {b₁ b₂ : bool} :
  sat g x b₁ →
  sat g x b₂ →
  b₁ = b₂ :=
begin
  intro h₁,
  cases h₁; intro h₂,
  { cases h₂, tauto },
  { cases h₂, tauto },
  { rw [ref.sat_root_iff] at h₁ h₂,
    have eq := node.sat_inj h₁ h₂,
    simp only [bxor_invol] at eq,
    simp [eq] }
end

def sat_right_unique (g : graph α) : relator.right_unique (sat g) :=
λ _ _ _ h, sat_inj h

theorem sat_of_subset {g g' : graph α} {x : ref α} {b : bool} :
  sat g x b →
  g ≤ g' →
  sat g' x b :=
begin
  intro h,
  cases h; intros,
  { constructor },
  { constructor },
  { constructor,
    apply node.sat_of_subset; assumption }
end

/-- Invert a `ref`. -/
@[simp]
protected def neg : ref α → ref α
| top        := bot
| bot        := top
| (root a b) := root a (!b)

@[reducible]
instance : has_neg (ref α) :=
⟨ref.neg⟩

lemma sat_neg_iff {g : graph α} {r : ref α} {b : bool} :
  sat g (-r) b ↔ sat g r (!b) :=
begin
  cases r with a b',
  { simp only [has_neg.neg, ref.neg],
    rw [ref.sat_top_iff, ref.sat_bot_iff],
    cases b; tauto },
  { simp only [has_neg.neg, ref.neg],
    rw [ref.sat_top_iff, ref.sat_bot_iff],
    cases b; tauto },
  { simp only [has_neg.neg, ref.neg, ref.sat_root_iff],
    suffices h : bxor (!b') b = bxor b' (!b), by rw [h],
    cases b'; cases b; tauto }
end

lemma neg_invol (x : ref α) : -(-x) = x :=
by cases x; simp [has_neg.neg, ref.neg]

end ref

section sat
variables {α : Type*} {sat : α → bool → Prop} (right_unique : relator.right_unique sat)
include right_unique

/-- A sat tt node is not sat ff. -/
theorem not_sat_ff_of_sat_tt {x : α} :
  sat x tt → ¬(sat x ff) :=
λ h₁ h₂, by cases right_unique h₁ h₂

/-- A sat ff node is not sat tt. -/
theorem not_sat_tt_of_sat_ff {x : α} :
  sat x ff → ¬(sat x tt) :=
λ h₁ h₂, by cases right_unique h₁ h₂

/-- A node that is not sat ff, but is sat b for some b, must be sat tt. -/
theorem sat_tt_of_not_sat_ff {x : α} {b : bool} :
  ¬(sat x ff) →
  sat x b →
  sat x tt :=
λ _ _ , by cases b; tauto

/-- A node that is not sat tt, but is sat b for some b, must be sat ff. -/
theorem sat_ff_of_not_sat_tt {x : α} {b : bool} :
  ¬(sat x tt) →
  sat x b →
  sat x ff :=
λ _ _ , by cases b; tauto

end sat

open hashable

/-- A node cache is represented using 4 nested tries. -/
abbreviation node_cache (α : Type*) : Type* := trien α 3

/-- A factory maintains the next ID for allocation, a list of (ID, node) pairs, and invariants. -/
structure factory (α σ : Type*) [unordered_map α (aig.node α) σ] [perfect_hashable α] [counter α] :=
(nextid   : α)
(nodes    : σ)
(cache    : node_cache α)
(cache_ok : ∀ (n₁ : α) (b₁ : bool) (n₂ : α) (b₂ : bool) (n₃ : α),
  cache.lookup (hash n₁ ::ᵥ hash b₁ ::ᵥ hash n₂ ::ᵥ hash b₂ ::ᵥ vector.nil) = some n₃ →
  unordered_map.lookup n₃ nodes = some (node.and n₁ b₁ n₂ b₂))
(complete : ∀ (x : α),
  x < nextid ↔ x ∈ (unordered_map.to_list nodes).keys)

namespace factory
variables {α σ : Type*} [unordered_map α (node α) σ] [counter α] [perfect_hashable α]

/--  Initialize an AIG factory. -/
protected def init : factory α σ :=
{ nextid   := counter.init,
  cache    := trien.nil,
  cache_ok := by { intros _ _ _ _ _ h, rw [trien.lookup_nil] at h, tauto },
  nodes    := unordered_map.empty,
  complete := by simp [unordered_map.empty_eq, counter.not_lt_init] }

instance : inhabited (factory α σ) :=
⟨factory.init⟩

instance : preorder (factory α σ) :=
{ le       := λ g₁ g₂, (unordered_map.to_list g₁.nodes) ⊆ (unordered_map.to_list g₂.nodes),
  le_refl  := by tauto,
  le_trans := by tauto }

lemma le_iff_nodes_subset (g₁ g₂ : factory α σ) :
  g₁ ≤ g₂ ↔ node.interpret g₁.nodes ≤ node.interpret g₂.nodes :=
begin
  simp only [has_le.le, preorder.le, node.interpret],
  split,
  { intros subset i n h,
    rw [← option.mem_def, unordered_map.mem_lookup_iff] at ⊢ h,
    apply subset h },
  { intros subset x h,
    cases x with n x,
    specialize @subset n x,
    simp only [← option.mem_def, unordered_map.mem_lookup_iff] at subset,
    exact subset h }
end

end factory
end aig
