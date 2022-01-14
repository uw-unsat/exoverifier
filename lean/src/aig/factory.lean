/-
Copyright (c) 2021 The UNSAT Group. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luke Nelson, Xi Wang
-/
import .basic
import .rewrite
import sat.factory

/-!
# AIG factory

This file provides support for creating AIG nodes.

## Implementation notes

The factory implements basic optimizations for constants (e.g., `mk_and`) to ensure no constants
as internal nodes.
-/

universe u

namespace aig
variables {α σ : Type u} [unordered_map α (node α) σ] [counter α] [perfect_hashable α]
open hashable

namespace factory

private lemma nextid_not_in_nodes_keys {n : α} {nodes : σ} :
  (∀ (x : α), x < n ↔ x ∈ (unordered_map.to_list nodes).keys) →
  n ∉ (unordered_map.to_list nodes).keys :=
begin
  intro h,
  rw ← h,
  simp
end

private lemma kinsert_nextid_complete {nodes : σ} {nextid : α} {newnode : node α} :
  (∀ (x : α), x < nextid ↔ x ∈ (unordered_map.to_list nodes).keys) →
  (∀ (x : α), x < counter.next nextid ↔ x ∈ (unordered_map.to_list (unordered_map.kinsert nextid newnode nodes)).keys) :=
begin
  intros complete x,
  simp only [list.keys, list.mem_map],
  simp only [unordered_map.mem_kinsert_iff],
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

/-- Create a fresh variable. -/
def mk_var (b : erased bool) : state (factory α σ) (ref α) :=
  state_t.mk $ λ g,
  let nodes' := node.insert_var g.nodes g.nextid b in
    (ref.mk_reg g.nextid, {
      nextid   := counter.next g.nextid,
      nodes    := nodes',
      cache_ok := by {
        intros n₁ b₁ n₂ b₂ n₃ lookup,
        simp only [nodes'],
        rw [← option.mem_def, node.insert_var, unordered_map.mem_lookup_iff, unordered_map.mem_kinsert_iff],
        left,
        have old_cache_ok := g.cache_ok,
        rw [← unordered_map.mem_lookup_iff, option.mem_def],
        apply old_cache_ok,
        from lookup },
      complete := by apply kinsert_nextid_complete g.complete,
      ..g })

lemma le_mk_var (b : erased bool) (g : factory α σ) :
  g ≤ ((mk_var b).run g).2 :=
begin
  rw le_iff_nodes_subset,
  apply node.subset_insert_var
end

lemma sat_mk_var (g g' : factory α σ) (b : erased bool) (r : ref α) :
  (mk_var b).run g = (r, g') →
  ref.sat (node.interpret g'.nodes) r b.out :=
begin
  intro mk,
  simp only [mk_var] at mk,
  cases mk,
  have b_eq_bxor_ff_b : b.out = (bxor ff b.out), by simp only [bool.bxor_ff_left],
  rw [b_eq_bxor_ff_b],
  apply ref.sat.root,
  simp only [ff_bxor],
  apply node.sat_insert_var,
  apply nextid_not_in_nodes_keys g.complete
end

/-- Create an AND operator without optimizations. -/
def mk_and_raw (a₁ : α) (b₁ : bool) (a₂ : α) (b₂ : bool) : state (factory α σ) (ref α) :=
state_t.mk $ λ g,
  (ref.mk_reg g.nextid, {
    nextid   := counter.next g.nextid,
    nodes    := node.insert_and g.nodes g.nextid a₁ b₁ a₂ b₂,
    cache    := g.cache.update (hash a₁ ::ᵥ hash b₁ ::ᵥ hash a₂ ::ᵥ hash b₂ ::ᵥ vector.nil) g.nextid,
    cache_ok := by {
      intros a₁' b₁' a₂' b₂' n₃' lookup,
      rw [← option.mem_def, trien.mem_lookup_iff, trien.mem_update_iff] at lookup,
      split_ifs at lookup,
      { subst lookup,
        repeat {rw [vector.cons_inj] at h},
        rcases h with ⟨h₁, h₂, h₃, h₄, h₅⟩,
        rw [perfect_hashable.hash_inj] at h₁ h₂ h₃ h₄,
        subst h₁, subst h₂, subst h₃, subst h₄,
        rw [← option.mem_def, unordered_map.mem_lookup_iff, node.insert_and, unordered_map.mem_kinsert_iff],
        right,
        refine ⟨_, rfl⟩,
        exact nextid_not_in_nodes_keys g.complete },
      { have old_cache_ok := g.cache_ok,
        rw [← option.mem_def, unordered_map.mem_lookup_iff, node.insert_and, unordered_map.mem_kinsert_iff],
        left,
        rw [← unordered_map.mem_lookup_iff, option.mem_def],
        apply old_cache_ok,
        rw [← option.mem_def, trien.mem_lookup_iff],
        exact lookup } },
    complete := by apply kinsert_nextid_complete g.complete,
    ..g } )

theorem le_mk_and_raw (a₁ : α) (b₁ : bool) (a₂ : α) (b₂ : bool) (g : factory α σ) :
  g ≤ ((mk_and_raw a₁ b₁ a₂ b₂).run g).2 :=
begin
  rw [mk_and_raw, le_iff_nodes_subset],
  apply node.subset_insert_and
end

theorem sat_mk_and_raw {g g' : factory α σ} {a₁ a₂ : α} {e₁ e₂ b₁ b₂ : bool} {r : ref α} :
  (mk_and_raw a₁ e₁ a₂ e₂).run g = (r, g') →
  ref.sat (node.interpret g.nodes) (ref.root a₁ e₁) b₁ →
  ref.sat (node.interpret g.nodes) (ref.root a₂ e₂) b₂ →
  ref.sat (node.interpret g'.nodes) r (b₁ && b₂) :=
begin
  intros hrun hsat₁ hsat₂,
  simp only [mk_and_raw, prod.mk.inj_iff] at hrun,
  cases hrun, subst_vars,
  rw [ref.sat_root_iff] at hsat₁ hsat₂ ⊢,
  rw [ff_bxor],
  have h := node.sat_insert_and (nextid_not_in_nodes_keys g.complete) hsat₁ hsat₂,
  repeat { rw [bxor_invol] at h },
  apply h
end

/-- Make an `and` node, returning a previously-cached id if the desired node is already created. -/
def mk_and_cache (a₁ : α) (b₁ : bool) (a₂ : α) (b₂ : bool) : state (factory α σ) (ref α) :=
state_t.mk $ λ g,
  /- Lookup in cache -/
  match g.cache.lookup (hash a₁ ::ᵥ hash b₁ ::ᵥ hash a₂ ::ᵥ hash b₂ ::ᵥ vector.nil) with
  | some r := (ref.mk_reg r, g)
  | none := (mk_and_raw a₁ b₁ a₂ b₂).run g
  end

lemma le_mk_and_cache (a₁ : α) (b₁ : bool) (a₂ : α) (b₂ : bool) (g : factory α σ) :
  g ≤ ((mk_and_cache a₁ b₁ a₂ b₂).run g).2 :=
begin
  rw [mk_and_cache],
  simp only,
  { cases g.cache.lookup (hash a₁ ::ᵥ hash b₁ ::ᵥ hash a₂ ::ᵥ hash b₂ ::ᵥ vector.nil),
    case none { apply le_mk_and_raw },
    case some { apply' le_refl } }
end

theorem sat_mk_and_cache {g g' : factory α σ} {a₁ a₂ : α} {e₁ e₂ b₁ b₂ : bool} {r : ref α} :
  (mk_and_cache a₁ e₁ a₂ e₂).run g = (r, g') →
  ref.sat (node.interpret g.nodes) (ref.root a₁ e₁) b₁ →
  ref.sat (node.interpret g.nodes) (ref.root a₂ e₂) b₂ →
  ref.sat (node.interpret g'.nodes) r (b₁ && b₂) :=
begin
  intros hrun hsat₁ hsat₂,
  simp only [mk_and_cache, prod.mk.inj_iff] at hrun,
  cases cache_h : g.cache.lookup (hash a₁ ::ᵥ hash e₁ ::ᵥ hash a₂ ::ᵥ hash e₂ ::ᵥ vector.nil),
  case none {
    rw [cache_h] at hrun,
    apply sat_mk_and_raw; assumption },
  case some : r {
    rw [cache_h] at hrun,
    cases hrun, clear hrun,
    have cached_and_lookup := g.cache_ok _ _ _ _ _ cache_h,
    clear cache_h,
    rw [ref.sat_root_iff] at hsat₁ hsat₂ ⊢,
    rw [ff_bxor],
    have h := node.sat.and (by exact cached_and_lookup) hsat₁ hsat₂,
    repeat { rw [bxor_invol] at h},
    exact h }
end

/-- Normalize the order of nodes before hitting the caching layer. -/
def mk_and_normorder (a₁ : α) (b₁ : bool) (a₂ : α) (b₂ : bool) : state (factory α σ) (ref α) :=
if a₂ ≤ a₁ then mk_and_cache a₁ b₁ a₂ b₂ else mk_and_cache a₂ b₂ a₁ b₁

lemma le_mk_and_normorder (a₁ : α) (b₁ : bool) (a₂ : α) (b₂ : bool) (g : factory α σ) :
  g ≤ ((mk_and_normorder a₁ b₁ a₂ b₂).run g).2 :=
begin
  rw [mk_and_normorder],
  split_ifs; apply le_mk_and_cache
end

theorem sat_mk_and_normorder {g g' : factory α σ} {a₁ a₂ : α} {e₁ e₂ b₁ b₂ : bool} {r : ref α} :
  (mk_and_normorder a₁ e₁ a₂ e₂).run g = (r, g') →
  ref.sat (node.interpret g.nodes) (ref.root a₁ e₁) b₁ →
  ref.sat (node.interpret g.nodes) (ref.root a₂ e₂) b₂ →
  ref.sat (node.interpret g'.nodes) r (b₁ && b₂) :=
begin
  intros hrun hsat₁ hsat₂,
  simp only [mk_and_normorder] at hrun,
  split_ifs at hrun,
  { apply sat_mk_and_cache; assumption },
  { rw [bool.band_comm b₁ b₂],
    apply sat_mk_and_cache; assumption }
end

/-- Helper function for `mk_and`, which invokes AIG optimization rules.
-/
def mk_and_aux (a₁ : α) (b₁ : bool) (a₂ : α) (b₂ : bool) : state (factory α σ) (ref α) := do
g ← get,
match unordered_map.lookup a₁ g.nodes, unordered_map.lookup a₂ g.nodes with
| some n₁, some n₂ :=
  match rewrite.optimize (node.interpret g.nodes) (a₁, b₁, n₁) (a₂, b₂, n₂) with
  | rewrite.result.sub r                           := pure r
  | rewrite.result.new (a₁', b₁', _) (a₂', b₂', _) := mk_and_normorder a₁' b₁' a₂' b₂'
  end
| _,       _      := mk_and_normorder a₁ b₁ a₂ b₂
end

theorem le_mk_and_aux (a₁ : α) (b₁ : bool) (a₂ : α) (b₂ : bool) (g : factory α σ) :
  g ≤ ((mk_and_aux a₁ b₁ a₂ b₂).run g).2 :=
begin
  cases h₁ : unordered_map.lookup a₁ g.nodes with n₁;
  cases h₂ : unordered_map.lookup a₂ g.nodes with n₂;
  simp only [mk_and_aux, get, state_t.get, monad_state.lift, pure_bind, state_t.run_bind];
  simp only [mk_and_aux._match_1, pure, id, h₁, h₂]; try { apply le_mk_and_normorder },
  cases rewrite.optimize (node.interpret g.nodes) (a₁, b₁, n₁) (a₂, b₂, n₂),
  case rewrite.result.sub {
    simp only [mk_and_aux._match_2, state_t.run_pure],
    simp only [pure, id], refl' },
  case rewrite.result.new : t₁' t₂' {
    rcases t₁' with ⟨a₁', b₁', _⟩,
    rcases t₂' with ⟨a₂', b₂', _⟩,
    simp only [mk_and_aux._match_2],
    apply le_mk_and_normorder }
end

theorem sat_mk_and_aux {g g' : factory α σ} {r : ref α} {a₁ a₂ : α} {b₁ b₂ r₁ r₂ : bool} :
  (mk_and_aux a₁ b₁ a₂ b₂).run g = (r, g') →
  (ref.root a₁ b₁).sat (node.interpret g.nodes) r₁ →
  (ref.root a₂ b₂).sat (node.interpret g.nodes) r₂ →
  r.sat (node.interpret g'.nodes) (r₁ && r₂) :=
begin
  cases ga₁ : unordered_map.lookup a₁ g.nodes with n₁;
  cases ga₂ : unordered_map.lookup a₂ g.nodes with n₂;
  simp only [mk_and_aux, get, state_t.get, monad_state.lift, pure_bind, state_t.run_bind];
  simp only [mk_and_aux._match_1, pure, id, ga₁, ga₂]; try { apply sat_mk_and_normorder },
  cases h : rewrite.optimize (node.interpret g.nodes) (a₁, b₁, n₁) (a₂, b₂, n₂),
  case rewrite.result.sub {
    simp only [mk_and_aux._match_2, state_t.run_pure],
    simp only [pure, id],
    rintro ⟨⟩ hsat₁ hsat₂,
    rcases rewrite.sat_optimize h ga₁ ga₂ hsat₁ hsat₂ with ⟨hsub, _⟩,
    apply hsub, refl },
  case rewrite.result.new : t₁' t₂' {
    rcases t₁' with ⟨a₁', b₁', n₁'⟩,
    rcases t₂' with ⟨a₂', b₂', n₂'⟩,
    simp only [mk_and_aux._match_2],
    intros hrun hsat₁ hsat₂,
    rcases rewrite.sat_optimize h ga₁ ga₂ hsat₁ hsat₂ with ⟨_, hnew⟩,
    rcases hnew rfl with ⟨ga₁', ga₂', r₁', r₂', hsat₁', hsat₂', heq⟩,
    rw [heq],
    exact sat_mk_and_normorder hrun hsat₁' hsat₂' }
end

/-- Create a logical operator `∧`. -/
def mk_and : ∀ (r₁ r₂ : ref α), state (factory α σ) (ref α)
| ref.bot          _                := pure ref.bot
| _                ref.bot          := pure ref.bot
| ref.top          r₂               := pure r₂
| r₁               ref.top          := pure r₁
| (ref.root a₁ b₁) (ref.root a₂ b₂) := if a₁ = a₂
  then pure $ if b₁ = b₂ then ref.root a₁ b₁ else ref.bot
  else mk_and_aux a₁ b₁ a₂ b₂

theorem le_mk_and (r₁ r₂ : ref α) (g : factory α σ) :
  g ≤ ((mk_and r₁ r₂).run g).2 :=
begin
  cases r₁ with a₁ b₁; cases r₂ with a₂ b₂; simp only [mk_and]; try { apply' le_refl },
  split_ifs with h₁ h₂,
  { rw [state_t.run_pure], apply' le_refl },
  { rw [state_t.run_pure], apply' le_refl },
  { apply le_mk_and_aux }
end

theorem sat_mk_and ⦃g g' : factory α σ⦄ (r₁ r₂ r₃ : ref α) {b₁ b₂ : bool} :
  (mk_and r₁ r₂).run g = (r₃, g') →
  ref.sat (node.interpret g.nodes) r₁ b₁ →
  ref.sat (node.interpret g.nodes) r₂ b₂ →
  ref.sat (node.interpret g'.nodes) r₃ (b₁ && b₂) :=
begin
  intros mk eval_r₁ eval_r₂,
  cases r₁ with a₁ e₁; cases r₂ with a₂ e₂; simp only [mk_and] at mk,
  { cases eval_r₁, cases eval_r₂, cases mk, constructor },
  { cases eval_r₁, cases eval_r₂, cases mk, constructor },
  { cases eval_r₁, cases mk, simpa },
  { cases eval_r₁, cases eval_r₂, cases mk, constructor },
  { cases eval_r₁, cases eval_r₂, cases mk, constructor },
  { cases eval_r₁, cases mk, simpa },
  { cases eval_r₂, cases mk, simpa },
  { cases eval_r₂, cases mk, simpa },
  split_ifs at mk with h₁ h₂ h₃; subst_vars,
  { cases mk,
    cases ref.sat_inj eval_r₁ eval_r₂,
    simp only [band_self, eval_r₁] },
  { cases mk,
    rw [ref.sat_root_iff] at eval_r₁ eval_r₂,
    have eq := node.sat_inj eval_r₁ eval_r₂,
    suffices : b₁ && b₂ = ff, by rw this; constructor,
    cases e₁; cases e₂; cases b₁; cases b₂; tauto },
  { apply sat_mk_and_aux mk; assumption }
end

/-- Create a logical operator `∨`. -/
def mk_or (r₁ r₂ : ref α) : state (factory α σ) (ref α) := do
ref.neg <$> mk_and (-r₁) (-r₂)

theorem le_mk_or (r₁ r₂ : ref α) (g : factory α σ) :
  g ≤ ((mk_or r₁ r₂).run g).2 :=
by { simp only [mk_or, state_t.run_map], apply le_mk_and }

theorem sat_mk_or ⦃g g' : factory α σ⦄ (r₁ r₂ r₃ : ref α) {b₁ b₂ : bool} :
  (mk_or r₁ r₂).run g = (r₃, g') →
  ref.sat (node.interpret g.nodes) r₁ b₁ →
  ref.sat (node.interpret g.nodes) r₂ b₂ →
  ref.sat (node.interpret g'.nodes) r₃ (b₁ || b₂) :=
begin
  intros mk eval_r₁ eval_r₂,
  simp only [mk_or, state_t.run_map] at mk,
  cases mk,
  simp only [ref.sat_neg_iff, bool.bnot_bor],
  apply sat_mk_and (-r₁) (-r₂),
  { rw [prod.mk.eta] },
  { simpa only [ref.sat_neg_iff, bnot_bnot] },
  { simpa only [ref.sat_neg_iff, bnot_bnot] }
end

instance : sat.factory (bref α) (factory α σ) :=
{ sat          := λ g x b, ref.sat (node.interpret g.nodes) x.1 b ∧ erased.mk b = x.2,
  default      := ⟨(ref.root counter.init tt, default)⟩,
  denote       := λ e, e.2,
  denote_sound := by {
    rintros g e x ⟨h₁, h₂⟩,
    rw [← h₂] },
  init_f       := aig.factory.init,
  sat_of_le    := λ g g' r _ l sat, by {
    cases sat with sat₁ h₁,
    rw [← h₁],
    refine ⟨_, rfl⟩,
    apply ref.sat_of_subset sat₁,
    rwa [le_iff_nodes_subset] at l } }

instance : sat.const_factory (bref α) (factory α σ) :=
{ mk_const     := λ _ b, cond b (ref.top, erased.mk tt) (ref.bot, erased.mk ff),
  sat_mk_const := λ _ b, by {
    cases b; split; constructor <|> refl } }

instance : sat.var_factory (bref α) (factory α σ) :=
{ mk_var       := λ b, (λ x, (x, b)) <$> mk_var b,
  le_mk_var    := le_mk_var,
  sat_mk_var   := λ g g' b r mk', by {
    simp only [state_t.run_map] at mk',
    cases mk',
    split,
    { exact sat_mk_var _ _ _ _ rfl },
    { simp only [erased.mk_out] } } }

@[reducible]
private def lift2 (f : bool → bool → bool) : erased bool → erased bool → erased bool :=
λ x y, x.bind $ λ x', y.bind $ λ y', erased.mk $ f x' y'

instance : sat.and_factory (bref α) (factory α σ) :=
{ mk_and       := λ r₁ r₂, (λ x, (x, lift2 band r₁.2 r₂.2)) <$> mk_and r₁.1 r₂.1,
  le_mk_and    := by {
    intros b₁ b₂,
    apply' factory.monad.increasing_map,
    apply le_mk_and },
  sat_mk_and   := by {
    intros _ _ _ _ _ _ _ mk sat₁ sat₂,
    cases sat₁ with sat₁ h₁,
    cases sat₂ with sat₂ h₂,
    simp only [state_t.run_map] at mk,
    cases mk,
    split,
    { exact sat_mk_and _ _ _ (by rw [prod.mk.eta]) sat₁ sat₂ },
    { simp only [← h₁, ← h₂, lift2, erased.bind_eq_out, erased.out_mk] } } }

instance : sat.or_factory (bref α) (factory α σ) :=
{ mk_or        := λ r₁ r₂, (λ x, (x, lift2 bor r₁.2 r₂.2)) <$> mk_or r₁.1 r₂.1,
  le_mk_or     := by {
    intros b₁ b₂,
    apply' factory.monad.increasing_map,
    apply le_mk_or },
  sat_mk_or    := by {
    intros _ _ _ _ _ _ _ mk sat₁ sat₂,
    cases sat₁ with sat₁ h₁,
    cases sat₂ with sat₂ h₂,
    simp only [state_t.run_map] at mk,
    cases mk,
    split,
    { exact sat_mk_or _ _ _ (by rw [prod.mk.eta]) sat₁ sat₂ },
    { simp only [← h₁, ← h₂, lift2, erased.bind_eq_out, erased.out_mk] } } }

instance : sat.not_factory (bref α) (factory α σ) :=
{ mk_not       := λ r, pure (-r.1, erased.map bnot r.2 ),
  le_mk_not    := by simp [factory.monad.increasing_pure],
  sat_mk_not   := λ g g' r₁ r₂ b mk' sat₁, by {
    simp only [factory.sat],
    cases sat₁ with sat₁ h₁,
    cases mk',
    split,
    { simpa only [ref.sat_neg_iff, bnot_bnot] },
    { simp only [← h₁, erased.map, erased.bind_eq_out, erased.out_mk] } } }

end factory

open semidecision.procedure

/-- Decide the evaluation of ref trivially by checking if it is ⊤ or ⊥ -/
def decide_via_trivial {ω : Type*} : factory.decision_procedure bool (bref α) (factory α σ) ω :=
begin
  refine sequence _ _,
  { apply @of_subset_procedure _ _ (λ (e : factory α σ × bref α × bool), e.2.1.1 = ref.top ∧ e.2.2 = tt),
    refine of_decidable_language,
    rintros ⟨_, ⟨_, _⟩, _⟩ ⟨⟨⟩, ⟨⟩⟩ _ ⟨h, ⟨⟩⟩,
    rw [ref.sat_top_iff] at h, subst h },
  { apply @of_subset_procedure _ _ (λ (e : factory α σ × bref α × bool), e.2.1.1 = ref.bot ∧ e.2.2 = ff),
    refine of_decidable_language,
    rintros ⟨_, ⟨_, _⟩, _⟩ ⟨⟨⟩, ⟨⟩⟩ _ ⟨h, ⟨⟩⟩,
    rw [ref.sat_bot_iff] at h, subst h }
end

end aig
