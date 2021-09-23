/-
Copyright (c) 2021 The UNSAT Group. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luke Nelson, Xi Wang
-/
import .basic
import .factory
import .inj
import data.hashable
import data.trie.basic

namespace btor

-- Lower-level interface
variables {β₀ γ₀ : Type} [smt.factory β₀ γ₀] [smt.add_factory β₀ γ₀] [smt.shl_factory β₀ γ₀]
open smt.add_factory smt.shl_factory

-- Higher-level interface
variables {α σ : Type} [unordered_map α (node α) σ] [counter α] [perfect_hashable α]
open unordered_map hashable

private structure compiler_state (β₀ γ₀ : Type*) :=
(mapping : trie β₀)
(factory : γ₀)

/-- Get the low-level expression associated with a particular id. -/
private def get_lower (i : α) : state_t (compiler_state β₀ γ₀) option β₀ :=
state_t.get >>= λ s, state_t.lift $ s.mapping.lookup $ hash i

/-- Add one new expression to the compiler state. -/
private def insert_node (i : α) (ctor : state γ₀ β₀) :
  state_t (compiler_state β₀ γ₀) option punit :=
modify (λ s, let expr := ctor.run s.factory in
             { mapping := trie.kinsert (hash i) expr.1 s.mapping, factory := expr.2, ..s })

/-- Add a new node for a binary operator. -/
private def insert_binary_node (i l r : α) (ctor : β₀ → β₀ → state γ₀ β₀) :
  state_t (compiler_state β₀ γ₀) option punit := do
l' ← get_lower l,
r' ← get_lower r,
insert_node i (ctor l' r')

/-- Compile one node. -/
private def compile_one (i : α) : node α → state_t (compiler_state β₀ γ₀) option punit
| (node.add l r) := insert_binary_node i l r mk_add
| (node.shl l r) := insert_binary_node i l r mk_shl
| _ := state_t.lift none

/-- Compile all of the nodes in a list. -/
private def compile_many :
  list (Σ (_ : α), node α) → state_t (compiler_state β₀ γ₀) option punit :=
monad.mapm' (λ (p : Σ (_ : α), node α), compile_one p.1 p.2)

/-- Initial state for compiler. -/
private def init_state : compiler_state β₀ γ₀ :=
{ mapping := trie.nil,
  factory := factory.init_f (Σ n, fin n → bool) β₀ }

/-- Compile a BTOR (ref, factory) pair into another implementation of the SMT interfacing,
    returning an (expression, factory) pair of the new interface if successful. -/
def compile (r : ref α) (g : factory α σ) : option (β₀ × γ₀) :=
let init : compiler_state β₀ γ₀ := init_state,
    result : option (unit × compiler_state β₀ γ₀) := (compile_many (to_list g.nodes)).run init in
  result >>= (λ res, (λ x, (x, res.2.factory)) <$> (trie.lookup (hash r.1) res.2.mapping))

section proof

/-- Invariant relating the BTOR graph to the compiler state. -/
private def compiler_invariant (g : graph α) (c : compiler_state β₀ γ₀) : Prop :=
∀ ⦃i : α⦄ {e : β₀},
  e ∈ trie.lookup (hash i) c.mapping →
  ∀ {v : Σ n, fin n → bool} {g₀ : γ₀},
    c.factory ≤ g₀ →
    node.sat g i v →
    factory.sat g₀ e v

private theorem get_lower_iff {s s' : compiler_state β₀ γ₀} {i : α} {e : β₀} :
  (get_lower i).run s = some (e, s') ↔ (e ∈ trie.lookup (hash i) s.mapping ∧ s = s') :=
begin
  simp only [get_lower, state_t.lift, state_t.run_bind, pure_bind, option.bind_eq_some,
             state_t.run_get, option.mem_def],
  split; intros h,
  { rcases h with ⟨e, h₁, h₂⟩,
    cases h₂,
    tauto },
  { existsi e,
    tauto }
end

private theorem insert_node_ok {g : graph α} {n : node α} {f : state γ₀ β₀} {i : α}
    {s s' : compiler_state β₀ γ₀} :
  factory.monad.increasing f →
  (∀ {g₀ v}, s.factory ≤ g₀ → node.sat g i v → factory.sat (f.run g₀).snd (f.run g₀).fst v) →
  g i = some n →
  compiler_invariant g s →
  (insert_node i f).run s = some (punit.star, s') →
  compiler_invariant g s' :=
begin
  intros f_inc sat_ok g_i inv mk,
  simp only [insert_node, state_t.run_bind] at mk,
  cases mk, clear mk,
  simp only [compiler_invariant],
  intros i' e' lookup v₁ g₀ leh sat₁,
  simp only [trie.mem_lookup_iff, trie.mem_kinsert_iff] at lookup,
  cases lookup,
  case inl {
    refine inv _ (le_trans f_inc leh) sat₁,
    simp only [trie.mem_lookup_iff],
    exact lookup },
  case inr {
    rcases lookup with ⟨notin, key_eq, val_eq⟩,
    rw [perfect_hashable.hash_inj] at key_eq,
    subst key_eq,
    rw [heq_iff_eq] at val_eq,
    subst val_eq,
    exact factory.sat_of_le leh (sat_ok (by refl) sat₁) }
end

private theorem insert_binary_node_ok {g : graph α} {n : node α} {f : β₀ → β₀ → state γ₀ β₀}
    (rt : ℕ → ℕ → part ℕ)
    (f' : ∀ {n₁ n₂ : ℕ} (h : (rt n₁ n₂).dom), (fin n₁ → bool) → (fin n₂ → bool) → fin ((rt n₁ n₂).get h) → bool)
    {i l r : α} {s s' : compiler_state β₀ γ₀} :
  (∀ x y, factory.monad.increasing (f x y)) →
  (∀ {v}, node.sat g i v →
    ∃ (n₁ n₂ : ℕ) (v₁ : fin n₁ → bool) (v₂ : fin n₂ → bool) (h : (rt n₁ n₂).dom),
      node.sat g l ⟨n₁, v₁⟩ ∧
      node.sat g r ⟨n₂, v₂⟩ ∧
      v = ⟨(rt n₁ n₂).get h, f' h v₁ v₂⟩) →
  (∀ {g₀ g₁ : γ₀} {n₁ n₂ : ℕ} (h : (rt n₁ n₂).dom) {v₁ v₂ v₃ : β₀} {r₁ : fin n₁ → bool} {r₂ : fin n₂ → bool},
    s.factory ≤ g₀ →
    (f v₁ v₂).run g₀ = (v₃, g₁) →
    factory.sat g₀ v₁ (⟨n₁, r₁⟩ : Σ n, fin n → bool) →
    factory.sat g₀ v₂ (⟨n₂, r₂⟩ : Σ n, fin n → bool) →
    factory.sat g₁ v₃ (⟨(rt n₁ n₂).get h, f' h r₁ r₂⟩ : Σ n, fin n → bool)) →
  g i = some n →
  compiler_invariant g s →
  (insert_binary_node i l r f).run s = some (punit.star, s') →
  compiler_invariant g s' :=
begin
  intros f_inc hisat_ok losat_ok g_i inv mk,
  simp only [insert_binary_node, state_t.run_bind, option.bind_eq_some, prod.exists] at mk,
  rcases mk with ⟨l', s₁, l_h, r', s₂, r_h, mk⟩,
  rw [get_lower_iff] at l_h r_h,
  cases r_h with r_h heq, subst heq,
  cases l_h with l_h heq, subst heq,
  refine insert_node_ok (@f_inc l' r') _ g_i inv mk,
  intros g₀ v hle sat₂,
  obtain ⟨n₁, n₂, v₁, v₂, h, sat_l, sat_r, h_v⟩ := hisat_ok sat₂,
  subst v,
  exact losat_ok h hle (by rw [prod.mk.eta]) (inv l_h hle sat_l) (inv r_h hle sat_r)
end

private theorem compile_one_ok {g : graph α} {s s' : compiler_state β₀ γ₀} {i : α} {n : node α} :
  compiler_invariant g s →
  g i = some n →
  (compile_one i n).run s = some (punit.star, s') →
  compiler_invariant g s' :=
begin
  intros inv lookup mk,
  cases n,
  case add : l r {
    simp only [compile_one] at mk,
    apply insert_binary_node_ok (λ x y, ⟨x = y, λ _, y⟩) (λ _ _ h v₁ v₂, bv.add (h.rec_on v₁) v₂) _ _ _ lookup inv mk,
    { apply le_mk_add },
    { intros v sat₂,
      rw [node.sat_add_iff lookup] at sat₂,
      rcases sat₂ with ⟨n, v₁, v₂, sat_v₁, sat_v₂, h⟩,
      subst h,
      existsi [n, n, v₁, v₂, rfl, sat_v₁, sat_v₂],
      congr },
    { intros _ _ _ _ h _ _ _ _ _ hle mk sat₁ sat₂,
      simp only at h, subst h,
      exact sat_mk_add mk sat₁ sat₂ } },
  case shl : l r {
    simp only [compile_one] at mk,
    apply insert_binary_node_ok (λ x y, ⟨⊤, λ _, x⟩) (λ _ _ _ v₁ v₂, bv.shl v₁ v₂) _ _ _ lookup inv mk,
    { apply le_mk_shl },
    { intros v sat₂,
      rw [node.sat_shl_iff lookup] at sat₂,
      rcases sat₂ with ⟨n₁, n₂, v₁, v₂, sat_v₁, sat_v₂, h⟩,
      subst h,
      existsi [n₁, n₂, v₁, v₂, true.intro, sat_v₁, sat_v₂],
      congr },
    { intros _ _ _ _ h _ _ _ _ _ hle mk sat₁ sat₂,
      exact sat_mk_shl mk sat₁ sat₂ } },
  all_goals { cases mk }
end

private theorem compile_many_ok (g : graph α) {l : list (Σ (_ : α), node α)} :
  ∀ {s s' : compiler_state β₀ γ₀},
    compiler_invariant g s →
    (∀ (i : Σ (_ : α), node α), i ∈ l → g i.fst = some i.snd) →
    (compile_many l).run s = some (punit.star, s') →
    compiler_invariant g s' :=
begin
  induction l,
  case nil {
    intros _ _ inv _ mk,
    cases mk,
    exact inv },
  case cons : x xs ih {
    intros _ _ inv h mk,
    simp only [compile_many, monad.mapm', mmap', has_bind.and_then, state_t.run_bind,
               option.bind_eq_some, prod.exists] at mk,
    rcases mk with ⟨u, _, one, rest⟩,
    cases u,
    simp only [compile_many, monad.mapm', mmap'] at ih,
    refine ih (compile_one_ok inv _ one) _ rest,
    { apply h,
      exact or.inl rfl },
    { intros _ h_xs,
      apply h,
      exact or.inr h_xs } }
end

private theorem init_state_ok {g : graph α} :
  compiler_invariant g (init_state : compiler_state β₀ γ₀) :=
begin
  intros _ _ h,
  exfalso,
  rw [init_state, trie.mem_lookup_iff] at h,
  cases h
end

theorem compile_sound {r : ref α} {g : factory α σ} {e : β₀} {g' : γ₀} {v₁ : Σ n, fin n → bool} :
  compile r g = some (e, g') →
  ref.sat (node.interpret g.nodes) r v₁ →
  factory.sat g' e v₁ :=
begin
  intros compile₁ sat₂,
  simp only [compile, option.bind_eq_some, prod.mk.inj_iff, option.map_eq_map, option.map_eq_some',
             prod.exists] at compile₁,
  rcases compile₁ with ⟨u, s, h₁, a, h₂, h₃, h₄⟩,
  subst h₃,
  subst h₄,
  cases u,
  have h₃ := compile_many_ok (node.interpret g.nodes) init_state_ok _ h₁,
  { cases sat₂ with sat₂ e,
    exact h₃ h₂ (le_refl _) sat₂ },
  { intros _ _,
    simpa only [node.interpret, ← option.mem_def, mem_lookup_iff, sigma.eta] }
end

end proof

section decision
variables {ω : Type} (decider : smt.decision_procedure β₀ γ₀ ω)
include decider

def decide_via_compile : smt.decision_procedure (ref α) (factory α σ) ω :=
begin
  rintros ⟨g, e, v₂⟩ w,
  rcases compile : (compile e g : option (β₀ × γ₀)) with _ | ⟨e₀, g₀⟩,
  { -- Compilation failed: unknown satisfiability.
    exact semidecision.unknown },
  apply (decider (g₀, (e₀, v₂)) w).modus_ponens,
  simp only [factory.sat],
  intros h _ sat₁,
  exact h _ (compile_sound compile sat₁)
end

end decision
end btor
