/-
Copyright (c) 2021 The UNSAT Group. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luke Nelson, Xi Wang
-/
import .basic
import smt.factory
import data.unordered_map.basic
import data.counter

namespace btor
universe u

/-- A factory maintains the next ID for allocation, a list of (ID, node) pairs, and invariants. -/
structure factory (α σ : Type*) [unordered_map α (node α) σ] [counter α] :=
(nextid    : α)
(nodes  : σ)
(complete : ∀ (x : α),
  x < nextid ↔ x ∈ (unordered_map.to_list nodes).keys)

namespace factory
variables {α σ : Type u} [unordered_map α (node α) σ] [counter α]
open unordered_map

/-- Create an initial SMT factory. -/
protected def init : factory α σ :=
{ nextid   := counter.init,
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
    rw [← option.mem_def, mem_lookup_iff] at ⊢ h,
    apply subset h },
  { intros subset x h,
    cases x with n x,
    specialize @subset n x,
    simp only [← option.mem_def, mem_lookup_iff] at subset,
    tauto }
end

private lemma kinsert_nextid_complete {nodes : σ} {nextid : α} {newnode : node α} :
  (∀ (x : α), x < nextid ↔ x ∈ (to_list nodes).keys) →
  (∀ (x : α), x < counter.next nextid ↔ x ∈ (to_list (kinsert nextid newnode nodes)).keys) :=
begin
  intros complete x,
  simp only [list.keys, list.mem_map],
  simp only [mem_kinsert_iff],
  by_cases x = nextid,
  { subst_vars,
    simp only [counter.lt_next, true_iff],
    existsi sigma.mk x newnode,
    specialize complete x,
    simp only [lt_self_iff_false, false_iff] at complete,
    simp [complete] },
  { rw [counter.ne_implies_lt_add_one_iff_lt h, complete],
    simp only [list.keys, list.mem_map],
    split; rintro ⟨n, h₁, h₂⟩; existsi n,
    { tauto },
    { cases h₁, { tauto }, { cc } } }
end

private lemma nextid_not_in_nodes_keys {n : α} {nodes : σ} :
  (∀ (x : α), x < n ↔ x ∈ (unordered_map.to_list nodes).keys) →
  n ∉ (unordered_map.to_list nodes).keys :=
begin
  intro h,
  rw ← h,
  simp
end

def mk_var ⦃n : ℕ⦄ (f : erased (fin n → bool)) : state (factory α σ) (ref α) :=
state_t.mk $ λ g,
  ((g.nextid, (⟨n, f⟩ : Σ n, erased (fin n → bool))),
    { nodes    := kinsert g.nextid (node.var f) g.nodes,
      nextid   := counter.next g.nextid,
      complete := by apply kinsert_nextid_complete g.complete, ..g })

theorem le_mk_var ⦃n : ℕ⦄ ⦃f : erased (fin n → bool)⦄ ⦃g : factory α σ⦄ :
  g ≤ ((mk_var f).run g).2 :=
by rw [le_iff_nodes_subset]; apply node.subset_insert

theorem sat_mk_var ⦃g g' : factory α σ⦄ {n : ℕ} {f : erased (fin n → bool)} {e : ref α} :
  (mk_var f).run g = (e, g') →
  ref.sat (node.interpret g'.nodes) e ⟨n, f.out⟩ :=
begin
  intros mk, cases mk,
  split,
  { apply node.sat.var,
    apply node.interpret_insert,
    apply nextid_not_in_nodes_keys g.complete },
  { simp only [ref.denotation, erased.bind_eq_out, erased.out_mk],
    tauto }
end

def mk_const ⦃n : ℕ⦄ (v : lsbvector n) : state (factory α σ) (ref α) :=
state_t.mk $ λ g,
  ((g.nextid, ⟨n, erased.mk v.nth⟩),
    { nodes    := kinsert g.nextid (node.const v) g.nodes,
      nextid   := counter.next g.nextid,
      complete := by apply kinsert_nextid_complete g.complete, ..g })

theorem le_mk_const ⦃n : ℕ⦄ ⦃v : lsbvector n⦄ ⦃g : factory α σ⦄ :
  g ≤ ((mk_const v).run g).2 :=
by rw [le_iff_nodes_subset]; apply node.subset_insert

theorem sat_mk_const ⦃g g' : factory α σ⦄ {n : ℕ} {v : lsbvector n} {e : ref α} :
  (mk_const v).run g = (e, g') →
  ref.sat (node.interpret g'.nodes) e ⟨n, v.nth⟩ :=
begin
  intros mk, cases mk,
  split,
  { apply node.sat.const,
    apply node.interpret_insert,
    apply nextid_not_in_nodes_keys g.complete },
  { simp only [ref.denotation, erased.out_mk, erased.bind_eq_out],
    tauto }
end

def mk_unary_op
  (r : ℕ → ℕ)
  (f : ∀ ⦃n : ℕ⦄, (fin n → bool) → fin (r n) → bool)
  (k : α → node α) :
  ref α → state (factory α σ) (ref α)
| ⟨i₁, ⟨n₁, v₁⟩⟩ :=
  state_t.mk $ λ g,
    ((g.nextid,
      ⟨r n₁, v₁.bind (λ v₁', erased.mk $ f v₁')⟩),
      { nodes    := kinsert g.nextid (k i₁) g.nodes,
        nextid   := counter.next g.nextid,
        complete := by apply kinsert_nextid_complete g.complete, ..g })

theorem le_mk_unary_op
  (r : ℕ → ℕ)
  (f : ∀ ⦃n : ℕ⦄, (fin n → bool) → fin (r n) → bool)
  (k : α → node α)
  {e₁ : ref α} ⦃g : factory α σ⦄ :
  g ≤ ((mk_unary_op r f k e₁).run g).2 :=
begin
  rw [le_iff_nodes_subset],
  rcases e₁ with ⟨i₁, ⟨n₁, v₁⟩⟩,
  apply node.subset_insert
end

/-- A generic version of the constructor for `node.eval` on unary operators. -/
private abbreviation unary_sat
  (r : ℕ → ℕ)
  (f : ∀ ⦃n : ℕ⦄, (fin n → bool) → fin (r n) → bool)
  (k : α → node α) : Prop :=
∀ {g : graph α} {a a₁ : α} {n : ℕ} {v₁ : fin n → bool},
g a = some (k a₁) →
node.sat g a₁ ⟨n, v₁⟩ →
node.sat g a  ⟨r n, f v₁⟩

theorem sat_mk_unary_op
  (r : ℕ → ℕ)
  (f : ∀ ⦃n : ℕ⦄, (fin n → bool) → fin (r n) → bool)
  ⦃k : α → node α⦄
  (h : unary_sat r f k)
  ⦃g g' : factory α σ⦄ {e₁ e₂ : ref α} {n : ℕ} {v₁ : fin n → bool} :
  (mk_unary_op r f k e₁).run g = (e₂, g') →
  ref.sat (node.interpret g.nodes)  e₁ ⟨n, v₁⟩ →
  ref.sat (node.interpret g'.nodes) e₂ ⟨r n, f v₁⟩ :=
begin
  intros mk sat₁,
  cases sat₁ with sat₁ eq₁,
  rcases e₁ with ⟨i₁, ⟨n₁, v₁⟩⟩,
  simp only [ref.denotation, erased.bind_eq_out, erased.out_mk] at eq₁,
  rcases eq₁ with ⟨eq₁_l, eq₁_r⟩,
  subst eq₁_l,
  rw [heq_iff_eq] at eq₁_r, subst eq₁_r,
  simp only [mk_unary_op] at mk,
  cases mk,
  split,
  { apply h,
    { simp only [node.interpret],
      apply node.interpret_insert,
      apply nextid_not_in_nodes_keys g.complete },
    { apply node.sat_of_subset sat₁,
      apply node.subset_insert } },
  { simp only [ref.denotation, erased.bind_eq_out, erased.out_mk],
    tauto }
end

def mk_binary_op
  {r : ℕ → ℕ}
  (f : ∀ ⦃n : ℕ⦄, (fin n → bool) → (fin n → bool) → fin (r n) → bool)
  (k : α → α → node α) :
  ref α → ref α → state (factory α σ) (ref α)
| ⟨i₁, ⟨n₁, v₁⟩⟩ ⟨i₂, ⟨n₂, v₂⟩⟩ :=
  state_t.mk $ λ g,
    ((g.nextid,
      ⟨r n₁,
        v₁.bind (λ v₁',
          v₂.bind (λ v₂',
            erased.mk $ λ (i : fin (r n₁)), dite (n₁ = n₂) (λ h, f v₁' (eq.rec_on h.symm v₂') i) (λ _, default _)))⟩),
      { nodes    := kinsert g.nextid (k i₁ i₂) g.nodes,
        nextid   := counter.next g.nextid,
        complete := by apply kinsert_nextid_complete g.complete, ..g })

theorem le_mk_binary_op
  {r : ℕ → ℕ}
  (f : ∀ ⦃n : ℕ⦄, (fin n → bool) → (fin n → bool) → fin (r n) → bool)
  (k : α → α → node α)
  {e₁ e₂ : ref α} ⦃g : factory α σ⦄ :
  g ≤ ((mk_binary_op f k e₁ e₂).run g).2 :=
begin
  rw [le_iff_nodes_subset],
  rcases e₁ with ⟨i₁, ⟨n₁, v₁⟩⟩,
  rcases e₂ with ⟨i₂, ⟨n₂, v₂⟩⟩,
  apply node.subset_insert
end

/-- A generic version of the constructor for `node.eval` on binary operators. -/
private abbreviation binary_sat
  {r : ℕ → ℕ}
  (f : ∀ ⦃n : ℕ⦄, (fin n → bool) → (fin n → bool) → fin (r n) → bool)
  (k : α → α → node α) : Prop :=
∀ {g : graph α} {a a₁ a₂ : α} {n : ℕ} {v₁ : fin n → bool} {v₂ : fin n → bool},
g a = some (k a₁ a₂) →
node.sat g a₁ ⟨n, v₁⟩ →
node.sat g a₂ ⟨n, v₂⟩ →
node.sat g a  ⟨r n, f v₁ v₂⟩

theorem sat_mk_binary_op
  {r : ℕ → ℕ}
  (f : ∀ ⦃n : ℕ⦄, (fin n → bool) → (fin n → bool) → fin (r n) → bool)
  ⦃k : α → α → node α⦄
  (h : binary_sat f k)
  ⦃g g' : factory α σ⦄ {e₁ e₂ e₃ : ref α} {n : ℕ} {v₁ : fin n → bool} {v₂ : fin n → bool} :
  (mk_binary_op f k e₁ e₂).run g = (e₃, g') →
  ref.sat (node.interpret g.nodes)  e₁ ⟨n, v₁⟩ →
  ref.sat (node.interpret g.nodes)  e₂ ⟨n, v₂⟩ →
  ref.sat (node.interpret g'.nodes) e₃ ⟨r n, f v₁ v₂⟩ :=
begin
  intros mk sat₁ sat₂,
  cases sat₁ with sat₁ eq₁,
  cases sat₂ with sat₂ eq₂,
  rcases e₁ with ⟨i₁, ⟨n₁, v₁⟩⟩,
  rcases e₂ with ⟨i₂, ⟨n₂, v₂⟩⟩,
  simp only [ref.denotation, erased.bind_eq_out, erased.out_mk] at eq₁,
  rcases eq₁ with ⟨eq₁_l, eq₁_r⟩,
  subst eq₁_l,
  rw [heq_iff_eq] at eq₁_r, subst eq₁_r,
  simp only [ref.denotation, erased.bind_eq_out, erased.out_mk] at eq₂,
  rcases eq₂ with ⟨eq₂_l, eq₂_r⟩,
  subst eq₂_l,
  rw [heq_iff_eq] at eq₂_r, subst eq₂_r,
  simp only [mk_binary_op, erased.bind_def, erased.bind_eq_out, erased.out_mk] at mk,
  simp_rw [dif_pos rfl] at mk,
  cases mk,
  split,
  { apply h,
    { simp only [node.interpret],
      apply node.interpret_insert,
      apply nextid_not_in_nodes_keys g.complete },
    { apply node.sat_of_subset sat₁,
      apply node.subset_insert },
    { apply node.sat_of_subset sat₂,
      apply node.subset_insert } },
  { simp only [ref.denotation, erased.bind_eq_out, erased.out_mk],
    tauto }
end

def mk_shift_op
  (f : ∀ ⦃n₁ n₂ : ℕ⦄, (fin n₁ → bool) → (fin n₂ → bool) → fin n₁ → bool)
  (k : α → α → node α) :
  ref α → ref α → state (factory α σ) (ref α)
| ⟨i₁, ⟨n₁, v₁⟩⟩ ⟨i₂, ⟨n₂, v₂⟩⟩ :=
  state_t.mk $ λ g,
    ((g.nextid,
      ⟨n₁,
        v₁.bind (λ v₁',
          v₂.bind (λ v₂',
            erased.mk (f v₁' v₂')))⟩),
      { nodes    := kinsert g.nextid (k i₁ i₂) g.nodes,
        nextid   := counter.next g.nextid,
        complete := by apply kinsert_nextid_complete g.complete, ..g })

theorem le_mk_shift_op
  (f : ∀ ⦃n₁ n₂ : ℕ⦄, (fin n₁ → bool) → (fin n₂ → bool) → fin n₁ → bool)
  (k : α → α → node α)
  {e₁ e₂ : ref α} ⦃g : factory α σ⦄ :
  g ≤ ((mk_shift_op f k e₁ e₂).run g).2 :=
begin
  rw [le_iff_nodes_subset],
  rcases e₁ with ⟨i₁, ⟨n₁, v₁⟩⟩,
  rcases e₂ with ⟨i₂, ⟨n₂, v₂⟩⟩,
  apply node.subset_insert
end

/-- A generic version of the constructor for `node.eval` on binary operators. -/
private abbreviation shift_sat
  (f : ∀ ⦃n₁ n₂ : ℕ⦄, (fin n₁ → bool) → (fin n₂ → bool) → fin n₁ → bool)
  (k : α → α → node α) : Prop :=
∀ {g : graph α} {a a₁ a₂ : α} {n₁ n₂ : ℕ} {v₁ : fin n₁→ bool} {v₂ : fin n₂ → bool},
g a = some (k a₁ a₂) →
node.sat g a₁ ⟨n₁, v₁⟩ →
node.sat g a₂ ⟨n₂, v₂⟩ →
node.sat g a  ⟨n₁, f v₁ v₂⟩

theorem sat_mk_shift_op
  (f : ∀ ⦃n₁ n₂ : ℕ⦄, (fin n₁ → bool) → (fin n₂ → bool) → fin n₁ → bool)
  ⦃k : α → α → node α⦄
  (h : shift_sat f k)
  ⦃g g' : factory α σ⦄ {e₁ e₂ e₃ : ref α} {n₁ n₂ : ℕ} {v₁ : fin n₁ → bool} {v₂ : fin n₂ → bool} :
  (mk_shift_op f k e₁ e₂).run g = (e₃, g') →
  ref.sat (node.interpret g.nodes)  e₁ ⟨n₁, v₁⟩ →
  ref.sat (node.interpret g.nodes)  e₂ ⟨n₂, v₂⟩ →
  ref.sat (node.interpret g'.nodes) e₃ ⟨n₁, f v₁ v₂⟩ :=
begin
  intros mk sat₁ sat₂,
  cases sat₁ with sat₁ eq₁,
  cases sat₂ with sat₂ eq₂,
  rcases e₁ with ⟨i₁, ⟨n₁, v₁⟩⟩,
  rcases e₂ with ⟨i₂, ⟨n₂, v₂⟩⟩,
  simp only [ref.denotation, erased.bind_eq_out, erased.out_mk] at eq₁,
  rcases eq₁ with ⟨eq₁_l, eq₁_r⟩,
  subst eq₁_l,
  rw [heq_iff_eq] at eq₁_r, subst eq₁_r,
  simp only [ref.denotation, erased.bind_eq_out, erased.out_mk] at eq₂,
  rcases eq₂ with ⟨eq₂_l, eq₂_r⟩,
  subst eq₂_l,
  rw [heq_iff_eq] at eq₂_r, subst eq₂_r,
  simp only [mk_shift_op] at mk,
  cases mk,
  split,
  { apply h,
    { simp only [node.interpret],
      apply node.interpret_insert,
      apply nextid_not_in_nodes_keys g.complete },
    { apply node.sat_of_subset sat₁,
      apply node.subset_insert },
    { apply node.sat_of_subset sat₂,
      apply node.subset_insert } },
  { simp only [ref.denotation, erased.bind_eq_out, erased.out_mk],
    tauto }
end

def mk_ite : ref α → ref α → ref α → state (factory α σ) (ref α)
| ⟨i₀, ⟨n₀, v₀⟩⟩ ⟨i₁, ⟨n₁, v₁⟩⟩ ⟨i₂, ⟨n₂, v₂⟩⟩ :=
  state_t.mk $ λ g,
    ((g.nextid,
      ⟨n₁,
        v₀.bind (λ v₀',
          v₁.bind (λ v₁',
            v₂.bind (λ v₂',
              erased.mk (λ (i : fin n₁), dite (n₁ = n₂) (λ h₁, dite (n₀ = 1) (λ h₂, bv.ite (h₂.rec_on v₀') v₁' (h₁.symm.rec_on v₂') i) (λ _, default _)) (λ _, default _)))))⟩),
      { nodes    := kinsert g.nextid (node.ite i₀ i₁ i₂) g.nodes,
        nextid   := counter.next g.nextid,
        complete := by apply kinsert_nextid_complete g.complete, ..g })

theorem le_mk_ite
  ⦃e₀ e₁ e₂ : ref α⦄ ⦃g : factory α σ⦄ :
  g ≤ ((mk_ite e₀ e₁ e₂).run g).2 :=
begin
  rw [le_iff_nodes_subset],
  rcases e₀ with ⟨i₀, ⟨n₀, v₀⟩⟩,
  rcases e₁ with ⟨i₁, ⟨n₁, v₁⟩⟩,
  rcases e₂ with ⟨i₂, ⟨n₂, v₂⟩⟩,
  apply node.subset_insert
end

theorem sat_mk_ite
  ⦃g g' : factory α σ⦄ {e₀ e₁ e₂ e₃ : ref α} {n : ℕ} {v₀ : fin 1 → bool} {v₁ v₂ : fin n → bool} :
  (mk_ite e₀ e₁ e₂).run g = (e₃, g') →
  ref.sat (node.interpret g.nodes)  e₀ ⟨1, v₀⟩ →
  ref.sat (node.interpret g.nodes)  e₁ ⟨n, v₁⟩ →
  ref.sat (node.interpret g.nodes)  e₂ ⟨n, v₂⟩ →
  ref.sat (node.interpret g'.nodes) e₃ ⟨n, bv.ite v₀ v₁ v₂⟩ :=
begin
  intros mk sat₀ sat₁ sat₂,
  cases sat₀ with sat₀ eq₀,
  cases sat₁ with sat₁ eq₁,
  cases sat₂ with sat₂ eq₂,
  rcases e₀ with ⟨i₀, ⟨n₀, v₀⟩⟩,
  rcases e₁ with ⟨i₁, ⟨n₁, v₁⟩⟩,
  rcases e₂ with ⟨i₂, ⟨n₂, v₂⟩⟩,
  simp only [ref.denotation, erased.bind_eq_out, erased.out_mk] at eq₀,
  rcases eq₀ with ⟨eq₀_l, eq₀_r⟩,
  subst eq₀_l,
  rw [heq_iff_eq] at eq₀_r, subst eq₀_r,
  simp only [ref.denotation, erased.bind_eq_out, erased.out_mk] at eq₁,
  rcases eq₁ with ⟨eq₁_l, eq₁_r⟩,
  subst eq₁_l,
  rw [heq_iff_eq] at eq₁_r, subst eq₁_r,
  simp only [ref.denotation, erased.bind_eq_out, erased.out_mk] at eq₂,
  rcases eq₂ with ⟨eq₂_l, eq₂_r⟩,
  subst eq₂_l,
  rw [heq_iff_eq] at eq₂_r, subst eq₂_r,
  simp only [mk_ite] at mk,
  simp only [mk_binary_op, erased.bind_def, erased.bind_eq_out, mk_ite, erased.out_mk] at mk,
  simp_rw [dif_pos rfl] at mk,
  cases mk,
  split,
  { apply node.sat.ite,
    { simp only [node.interpret],
      apply node.interpret_insert,
      apply nextid_not_in_nodes_keys g.complete },
    { apply node.sat_of_subset sat₀,
      apply node.subset_insert },
    { apply node.sat_of_subset sat₁,
      apply node.subset_insert },
    { apply node.sat_of_subset sat₂,
      apply node.subset_insert } },
  { simp only [ref.denotation, erased.bind_eq_out, erased.out_mk],
    tauto }
end

def mk_extract (upper lower : ℕ) : ref α → state (factory α σ) (ref α)
| ⟨i₁, ⟨n₁, v₁⟩⟩ :=
  state_t.mk $ λ g,
    ((g.nextid,
      ⟨upper - lower + 1,
        v₁.bind (λ v₁',
        erased.mk (λ i, dite (upper < n₁)
                            (λ h₁, dite (lower ≤ upper)
                                   (λ h₂, bv.extract upper lower h₁ h₂ v₁' i)
                                   (λ _, ff))
                            (λ _, ff)))⟩),
      { nodes    := kinsert g.nextid (node.extract upper lower i₁) g.nodes,
        nextid   := counter.next g.nextid,
        complete := by apply kinsert_nextid_complete g.complete, ..g })

theorem le_mk_extract ⦃upper lower : ℕ⦄ ⦃r : ref α⦄ ⦃g : factory α σ⦄ :
  g ≤ ((mk_extract upper lower r).run g).2 :=
by rw [le_iff_nodes_subset]; cases r with r₁ r₂; cases r₂; apply node.subset_insert

theorem sat_mk_extract ⦃g g' : factory α σ⦄ {e₁ e₂ : ref α} {upper lower n : ℕ} {v₁ : fin n → bool} :
  (mk_extract upper lower e₁).run g = (e₂, g') →
  ref.sat (node.interpret g.nodes) e₁ ⟨n, v₁⟩ →
  ∀ (h₁ : upper < n) (h₂ : lower ≤ upper),
    ref.sat (node.interpret g'.nodes) e₂ ⟨upper - lower + 1, bv.extract upper lower h₁ h₂ v₁⟩ :=
begin
  intros mk sat₁,
  cases sat₁ with sat₁ eq₁,
  rcases e₁ with ⟨i₁, ⟨n₁, v₁⟩⟩,
  simp only [ref.denotation, erased.bind_eq_out, erased.out_mk] at eq₁,
  rcases eq₁ with ⟨eq₁_l, eq₁_r⟩,
  subst eq₁_l,
  rw [heq_iff_eq] at eq₁_r, subst eq₁_r,
  intros h₁ h₂,
  simp only [mk_extract] at mk,
  simp only [mk_binary_op, erased.bind_def, erased.bind_eq_out, mk_extract, erased.out_mk] at mk,
  simp_rw [dif_pos h₁, dif_pos h₂] at mk,
  cases mk, clear mk,
  split,
  { apply node.sat.extract,
    { simp only [node.interpret],
      apply node.interpret_insert,
      apply nextid_not_in_nodes_keys g.complete },
    { apply node.sat_of_subset sat₁,
      apply node.subset_insert } },
  { simp only [ref.denotation, erased.bind_eq_out, erased.out_mk],
    tauto }
end

def mk_concat : ref α → ref α → state (factory α σ) (ref α)
| ⟨i₁, ⟨n₁, v₁⟩⟩ ⟨i₂, ⟨n₂, v₂⟩⟩ :=
  state_t.mk $ λ g,
    ((g.nextid,
      ⟨n₁ + n₂,
        v₁.bind (λ v₁',
          v₂.bind (λ v₂',
            erased.mk (bv.concat v₁' v₂')))⟩),
      { nodes    := kinsert g.nextid (node.concat i₁ i₂) g.nodes,
        nextid   := counter.next g.nextid,
        complete := by apply kinsert_nextid_complete g.complete, ..g })

theorem le_mk_concat
  ⦃e₁ e₂ : ref α⦄ ⦃g : factory α σ⦄ :
  g ≤ ((mk_concat e₁ e₂).run g).2 :=
begin
  rw [le_iff_nodes_subset],
  rcases e₁ with ⟨i₁, ⟨n₁, v₁⟩⟩,
  rcases e₂ with ⟨i₂, ⟨n₂, v₂⟩⟩,
  apply node.subset_insert
end

theorem sat_mk_concat
  ⦃g g' : factory α σ⦄ {e₁ e₂ e₃ : ref α} {n₁ n₂ : ℕ} {v₁ : fin n₁ → bool} {v₂ : fin n₂ → bool} :
  (mk_concat e₁ e₂).run g = (e₃, g') →
  ref.sat (node.interpret g.nodes)  e₁ ⟨n₁, v₁⟩ →
  ref.sat (node.interpret g.nodes)  e₂ ⟨n₂, v₂⟩ →
  ref.sat (node.interpret g'.nodes) e₃ ⟨n₁ + n₂, bv.concat v₁ v₂⟩ :=
begin
  intros mk sat₁ sat₂,
  cases sat₁ with sat₁ eq₁,
  cases sat₂ with sat₂ eq₂,
  rcases e₁ with ⟨i₁, ⟨n₁, v₁⟩⟩,
  rcases e₂ with ⟨i₂, ⟨n₂, v₂⟩⟩,
  simp only [ref.denotation, erased.bind_eq_out, erased.out_mk] at eq₁,
  rcases eq₁ with ⟨eq₁_l, eq₁_r⟩,
  subst eq₁_l,
  rw [heq_iff_eq] at eq₁_r, subst eq₁_r,
  simp only [ref.denotation, erased.bind_eq_out, erased.out_mk] at eq₂,
  rcases eq₂ with ⟨eq₂_l, eq₂_r⟩,
  subst eq₂_l,
  rw [heq_iff_eq] at eq₂_r, subst eq₂_r,
  simp only [mk_concat] at mk,
  cases mk, clear mk,
  split,
  { apply node.sat.concat,
    { simp only [node.interpret],
      apply node.interpret_insert,
      apply nextid_not_in_nodes_keys g.complete },
    { apply node.sat_of_subset sat₁,
      apply node.subset_insert },
    { apply node.sat_of_subset sat₂,
      apply node.subset_insert } },
  { simp only [ref.denotation, erased.bind_eq_out, erased.out_mk],
    tauto }
end

instance : smt.factory (ref α) (factory α σ) :=
{ sat          := λ g, ref.sat (node.interpret g.nodes),
  default      := ⟨(counter.init, ⟨0, erased.mk fin.elim0⟩)⟩,
  width        := λ _ i, i.2.1,
  width_sound  := by {
    rintros g e ⟨n, v⟩ ⟨_, h⟩,
    rw [h],
    simp only [ref.denotation, erased.bind_eq_out, erased.out_mk] },
  init_f       := btor.factory.init,
  sat_of_le    := by {
    intros _ _ _ _ h₁ h₂,
    cases h₂ with l r,
    subst r,
    refine and.intro _ rfl,
    apply node.sat_of_subset l,
    rw [← le_iff_nodes_subset],
    from h₁ },
  denote       := ref.denotation,
  denote_sound := by {
    rintros g e ⟨n, x⟩ ⟨h₁, h₂⟩,
    rw [h₂, erased.mk_out] } }

instance : smt.var_factory (ref α) (factory α σ) :=
{ mk_var     := mk_var,
  le_mk_var  := le_mk_var,
  sat_mk_var := sat_mk_var }

instance : smt.const_factory (ref α) (factory α σ) :=
{ mk_const     := mk_const,
  le_mk_const  := le_mk_const,
  sat_mk_const := sat_mk_const }

instance : smt.not_factory (ref α) (factory α σ) :=
{ mk_not     := mk_unary_op id @bv.not node.not,
  le_mk_not  := λ e₁, le_mk_unary_op id @bv.not node.not,
  sat_mk_not := sat_mk_unary_op id @bv.not (by apply node.sat.not) }

instance : smt.add_factory (ref α) (factory α σ) :=
{ mk_add     := mk_binary_op @bv.add node.add,
  le_mk_add  := λ e₁ e₂, le_mk_binary_op @bv.add node.add,
  sat_mk_add := sat_mk_binary_op @bv.add (by apply node.sat.add) }

instance : smt.and_factory (ref α) (factory α σ) :=
{ mk_and     := mk_binary_op @bv.and node.and,
  le_mk_and  := λ e₁ e₂, le_mk_binary_op @bv.and node.and,
  sat_mk_and := sat_mk_binary_op @bv.and (by apply node.sat.and) }

instance : smt.mul_factory (ref α) (factory α σ) :=
{ mk_mul     := mk_binary_op @bv.mul node.mul,
  le_mk_mul  := λ e₁ e₂, le_mk_binary_op @bv.mul node.mul,
  sat_mk_mul := sat_mk_binary_op @bv.mul (by apply node.sat.mul) }

instance : smt.udiv_factory (ref α) (factory α σ) :=
{ mk_udiv     := mk_binary_op @bv.udiv node.udiv,
  le_mk_udiv  := λ e₁ e₂, le_mk_binary_op @bv.udiv node.udiv,
  sat_mk_udiv := sat_mk_binary_op @bv.udiv (by apply node.sat.udiv) }

private abbreviation bveq {n : ℕ} (x y : fin n → bool) : fin 1 → bool :=
λ _, x = y

instance : smt.eq_factory (ref α) (factory α σ) :=
{ mk_eq     := mk_binary_op @bveq node.eq,
  le_mk_eq  := λ e₁ e₂, le_mk_binary_op @bveq node.eq,
  sat_mk_eq := sat_mk_binary_op @bveq (by apply node.sat.eq) }

private abbreviation bvult {n : ℕ} (x y : fin n → bool) : fin 1 → bool :=
λ _, x < y

instance : smt.ult_factory (ref α) (factory α σ) :=
{ mk_ult     := mk_binary_op @bvult node.ult,
  le_mk_ult  := λ e₁ e₂, le_mk_binary_op @bvult node.ult,
  sat_mk_ult := sat_mk_binary_op @bvult (by apply node.sat.ult) }

instance : smt.shl_factory (ref α) (factory α σ) :=
{ mk_shl     := mk_shift_op @bv.shl node.shl,
  le_mk_shl  := λ e₁ e₂, le_mk_shift_op @bv.shl node.shl,
  sat_mk_shl := sat_mk_shift_op @bv.shl (by apply node.sat.shl) }

instance : smt.lshr_factory (ref α) (factory α σ) :=
{ mk_lshr     := mk_shift_op @bv.lshr node.lshr,
  le_mk_lshr  := λ e₁ e₂, le_mk_shift_op @bv.lshr node.lshr,
  sat_mk_lshr := sat_mk_shift_op @bv.lshr (by apply node.sat.lshr) }

instance : smt.ite_factory (ref α) (factory α σ) :=
{ mk_ite     := mk_ite,
  le_mk_ite  := le_mk_ite,
  sat_mk_ite := sat_mk_ite }

instance : smt.extract_factory (ref α) (factory α σ) :=
{ mk_extract     := mk_extract,
  le_mk_extract  := le_mk_extract,
  sat_mk_extract := sat_mk_extract }

instance : smt.concat_factory (ref α) (factory α σ) :=
{ mk_concat     := mk_concat,
  le_mk_concat  := le_mk_concat,
  sat_mk_concat := sat_mk_concat }

end factory

end btor
