/-
Copyright (c) 2021 The UNSAT Group. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luke Nelson, Xi Wang
-/
import data.bv.concat
import misc.eq
import misc.fin
import misc.vector
import sat.factory
import ..factory

universe u

namespace smt
namespace bitblast
variables {β γ : Type u} [factory_instance : sat.factory β γ]
include factory_instance

open factory.monad

/-
  Implementation note: The recursive mk_* functions in this directory are written
  specifically to avoid triggering the use of well-founded recursion by the
  equation compiler, as it causese performance issues for kernel reduction.

  For example, in the function "mk_const" the recursive call is explicitly
  provided with the nat argument "@mk_const n (vector.tail v)" rather than
  "mk_const (vector.tail v)", as the latter uses wf recursion over vector,
  while the former uses structural indrecursionucion over nat.

  See src/misc/wf-example.lean for a simplified example of the problem.
-/

/-- Evaluation of vectors of circuits into (fin n → bool). -/
def eval (g : γ) {n₁ n₂ : ℕ} (v : vector β n₁) (f : fin n₂ → bool) : Prop :=
list.forall₂ (factory.sat g) v.to_list (list.of_fn f)

omit factory_instance
def cast_sigma (γ : Type*) [sat.factory β γ] : ∀ (m : ℕ) (v : Σ n, vector β n) , vector β m
| m ⟨n, v⟩ :=
  dite (n = m) (λ h, h.rec_on v) (λ _, vector.repeat (@inhabited.default β (factory.default bool γ)) m)
include factory_instance

namespace eval

protected theorem iff_forall₂ {g : γ} {n₁ n₂ : ℕ} {v : vector β n₁} {f : fin n₂ → bool} :
  eval g v f ↔ list.forall₂ (factory.sat g) v.to_list (list.of_fn f) :=
by refl

protected theorem iff_head_tail {g : γ} {n₁ n₂ : ℕ} {v : vector β (n₁ + 1)} {f : fin (n₂ + 1) → bool} :
  eval g v f ↔ (factory.sat g v.head (f 0) ∧ eval g v.tail (fin.tail f)) :=
begin
  rw [eval.iff_forall₂, ← vector.cons_head_tail v, ← fin.cons_self_tail f, vector.to_list_cons, list.of_fn_succ, list.forall₂_cons, fin.tail],
  simp only [iff_self, fin.cons_succ, vector.cons_head_tail, fin.tail_cons, eval.iff_forall₂]
end

protected theorem cons_iff {g : γ} {n₁ n₂ : ℕ} {a : β} {v : vector β n₁} {b : bool} {bs : fin n₂ → bool} :
  eval g (a ::ᵥ v) (fin.cons b bs) ↔ (factory.sat g a b ∧ eval g v bs) :=
by rw [eval.iff_head_tail, vector.cons_head, fin.cons_zero, vector.cons_tail, fin.tail_cons]

protected theorem length_eq {g : γ} {n₁ n₂ : ℕ} {v : vector β n₁} {f : fin n₂ → bool} :
  eval g v f → n₁ = n₂ :=
begin
  intro h,
  simp only [eval.iff_forall₂] at h,
  have h' := list.forall₂_length_eq h,
  rw [vector.to_list_length, list.length_of_fn] at h',
  from h'
end

protected theorem iff_nth {g : γ} {n : ℕ} {v : vector β n} {f : fin n → bool} :
  eval g v f ↔
  (∀ (i : fin n), factory.sat g (v.nth i) (f i)) :=
begin
  induction n,
  case zero {
    simp only [eval.iff_forall₂, vector.eq_nil v, vector.to_list_nil, list.forall₂_nil_left_iff,
               list.of_fn_zero, true_iff, eq_self_iff_true],
    refine fin.elim0 },
  case succ : _ ih {
    simp only [eval.iff_head_tail, ih, fin.forall_fin_succ, fin.tail, iff_self, vector.nth_zero,
               vector.nth_tail_succ] }
end

omit factory_instance
/-- Convert to a pure equality for the trivial factory interface. -/
protected theorem iff_trivial {n : ℕ} {v : vector bool n} {f : fin n → bool} :
  eval punit.star v f ↔ f = v.nth :=
by { simp only [eval.iff_nth, factory.sat, function.funext_iff], tauto }
include factory_instance

protected theorem to_head {g : γ} {n₁ n₂ : ℕ} {v : vector β (n₁ + 1)} {f : fin (n₂ + 1) → bool} :
  eval g v f →
  factory.sat g v.head (f 0) :=
by { rw [eval.iff_head_tail], exact λ ⟨h, _⟩, h }

protected theorem to_tail {g : γ} {n₁ n₂ : ℕ} {v : vector β (n₁ + 1)} {f : fin (n₂ + 1) → bool} :
  eval g v f →
  eval g v.tail (fin.tail f) :=
begin
  intro eval₁,
  have := (add_left_inj _).1 (eval.length_eq eval₁), subst n₂,
  simp only [eval.iff_nth] at eval₁ ⊢,
  intro i,
  rw [vector.nth_tail_succ],
  apply eval₁
end

protected theorem to_init {g : γ} {n₁ n₂ : ℕ} {v : vector β (n₁ + 1)} {f : fin (n₂ + 1) → bool} :
  eval g v f →
  eval g v.init (fin.init f) :=
begin
  intro eval₁,
  have := (add_left_inj _).1 (eval.length_eq eval₁), subst n₂,
  simp only [eval.iff_nth] at eval₁ ⊢,
  intro i,
  rw [vector.nth_init, fin.coe_eq_cast_succ],
  apply eval₁
end

protected theorem of_tail {g : γ} {n₁ n₂ : ℕ} {v : vector β (n₁ + 1)} {f : fin (n₂ + 1) → bool} :
  factory.sat g v.head (f 0) →
  eval g v.tail (fin.tail f) →
  eval g v f :=
begin
  intros h_head h_tail,
  rw [eval.iff_head_tail],
  exact ⟨h_head, h_tail⟩
end

protected theorem iff_singleton {g : γ} {v : vector β 1} {f : fin 1 → bool} :
  eval g v f ↔ factory.sat g v.head (f 0) :=
by simp [eval.iff_head_tail, eval, vector.eq_nil v.tail]

protected theorem of_le {g g' : γ} {n₁ n₂ : ℕ} {v : vector β n₁} {f : fin n₂ → bool} :
  g ≤ g' →
  eval g v f →
  eval g' v f :=
begin
  intros l h,
  have := eval.length_eq h, subst n₂,
  rw [eval.iff_nth] at h ⊢,
  intros i,
  exact factory.sat_of_le l (h i)
end

protected theorem snoc {g : γ} {n₁ n₂ : ℕ} {v : vector β n₁} {a : β} {bs : fin n₂ → bool} {b : bool} :
  eval g v bs →
  factory.sat g a b →
  eval g (v.snoc a) (fin.snoc bs b) :=
begin
  intros h₁ h₂,
  simp only [eval.iff_forall₂, vector.to_list_snoc, fin.list_of_fn_snoc],
  exact list.rel_append h₁ (list.forall₂.cons h₂ list.forall₂.nil)
end

protected theorem iff_init_last {g : γ} {n₁ n₂ : ℕ} {v : vector β (n₁ + 1)} {f : fin (n₂ + 1) → bool} :
  eval g v f ↔ (eval g v.init (fin.init f) ∧ factory.sat g v.last (f (fin.last n₂))) :=
begin
  split; intro h,
  { have := (add_left_inj _).1 (eval.length_eq h), subst n₂,
    split,
    { exact eval.to_init h },
    { rw [eval.iff_nth] at h,
      apply h } },
  { obtain ⟨h_init, h_last⟩ := h,
    rw [← vector.snoc_init_last v, ← fin.snoc_init_self f],
    exact eval.snoc h_init h_last }
end

protected theorem iff_eq_rec {g : γ} {n₁ n₂ n₁' n₂' : ℕ} {h₁ : n₁ = n₁'} {h₂ : n₂ = n₂'}
                             {v : vector β n₁} {f : fin n₂ → bool} :
  eval g v f ↔
  eval g (@eq.rec_on _ _ _ _ h₁ v) (@eq.rec_on _ _ _ _ h₂ f) :=
by subst_vars

protected theorem to_append {g : γ} {n₁ n₂ : ℕ} {v₁ : vector β n₁} {v₂ : vector β n₂}
                            {b₁ : fin n₁ → bool} {b₂ : fin n₂ → bool} :
  eval g v₁ b₁ →
  eval g v₂ b₂ →
  eval g (vector.append v₁ v₂) (bv.concat b₂ b₁) :=
begin
  simp only [eval.iff_forall₂],
  intros eval₁ eval₂,
  convert list.rel_append eval₁ eval₂,
  { simp },
  { rw [← bv.list_of_fn_concat] }
end

protected theorem iff_reverse {g : γ} {n₁ n₂ : ℕ} {v : vector β n₁} {b : fin n₂ → bool} :
  eval g v b ↔ eval g v.reverse (fin.reverse b) :=
by simp only [eval.iff_forall₂, vector.to_list_reverse, fin.list_of_fn_reverse, list.forall₂_reverse_iff]

protected theorem to_drop {g : γ} {n₁ n₂ : ℕ} (i : ℕ) {v : vector β n₁} {b : fin n₂ → bool} :
  eval g v b →
  eval g (v.drop i) (bv.drop i b) :=
begin
  simp only [eval.iff_forall₂],
  cases v with l,
  rw [vector.to_list_drop, vector.to_list_mk, bv.list_of_fn_drop],
  apply list.forall₂_drop
end

protected theorem to_take {g : γ} {n₁ n₂ : ℕ} (i : ℕ) {v : vector β n₁} {b : fin n₂ → bool} :
  eval g v b →
  eval g (v.take i) (bv.take i b) :=
begin
  simp only [eval.iff_forall₂],
  cases v with l,
  rw [vector.to_list_take, vector.to_list_mk, bv.list_of_fn_take],
  apply list.forall₂_take
end

theorem eval_cast_sigma {g : γ} {n₁ n₂ : ℕ} {v : vector β n₁} {f : fin n₂ → bool} :
  eval g v f →
  eval g (cast_sigma γ n₂ ⟨n₁, v⟩) f :=
begin
  intros eval₁,
  have c := eval.length_eq eval₁, subst c,
  simp only [cast_sigma],
  rw [dif_pos]; tauto
end

end eval

/-- A version of eval not indexed by the bitwidth: suitable for factory instances. -/
@[reducible]
def sat (g : γ) (v : Σ (n : ℕ), vector β n) (f : Σ (n : ℕ), fin n → bool) : Prop :=
eval g v.2 f.2

namespace sat

protected theorem iff_eval {g : γ} {e₁ : Σ n, vector β n} {v₁ : Σ n, fin n → bool} :
  sat g e₁ v₁ ↔ eval g e₁.2 v₁.2 :=
by refl

protected theorem iff_forall₂ {g : γ} {e₁ : Σ n, vector β n} {v₁ : Σ n, fin n → bool} :
  sat g e₁ v₁ ↔ list.forall₂ (factory.sat g) e₁.2.to_list (list.of_fn v₁.2) :=
by refl

def denote {n : ℕ} (v : vector β n) : erased (vector bool n) :=
v.mmap (λ (x : β), (factory.denote γ x : erased bool))

theorem denote_sound {g : γ} : ∀ {n₁ n₂ : ℕ} {v : vector β n₁} {f : fin n₂ → bool},
  sat g ⟨n₁, v⟩ ⟨n₂, f⟩ →
  n₁ = n₂ ∧ (@denote _ γ _ _ v).out.nth == f :=
begin
  intros n₁ n₂ v f sat₁,
  simp only [sat.iff_eval] at sat₁,
  have h := eval.length_eq sat₁, simp only at h, subst h,
  refine ⟨rfl, _⟩,
  rw [heq_iff_eq],
  simp only [denote],
  ext i,
  rw [eval.iff_nth] at sat₁,
  induction n₁,
  { refine fin.elim0 i },
  { rw [← vector.cons_head_tail v, vector.mmap_cons],
    simp only [erased.bind_def, erased.bind_eq_out, erased.pure_def, erased.out_mk],
    refine fin.cases _ _ i,
    { simp only [vector.nth_cons_zero, ← vector.nth_zero],
      rw [factory.denote_sound (sat₁ 0), erased.out_mk] },
    { intros j,
      simp only [vector.nth_cons_succ],
      rw [n₁_ih],
      intros j',
      simp only [vector.nth_tail_succ],
      exact sat₁ j'.succ } }
end

instance : smt.factory (Σ (n : ℕ), vector β n) γ :=
{ sat          := sat,
  default      := ⟨⟨0, vector.nil⟩⟩,
  denote       := λ ⟨n, expr⟩, (do
    v : vector bool n ← @denote _ γ _ _ expr,
    pure (⟨n, v.nth⟩ : Σ n, fin n → bool)),
  init_f       := (factory.init_f bool β : γ),
  denote_sound := by {
    rintros _ ⟨e₁, e₂⟩ ⟨x₁, x₂⟩ sat₁,
    simp only [smt.factory._match_1, erased.bind_def, erased.bind_eq_out, erased.pure_def],
    obtain ⟨a, b⟩ := denote_sound sat₁,
    subst a,
    congr,
    rw [heq_iff_eq] at b,
    exact b },
  width := λ _ ⟨n, _⟩, n,
  width_sound := by {
    rintros g ⟨n₁, e⟩ ⟨n₂, v⟩ sat₁,
    simp only [sat.iff_eval] at sat₁,
    have c := eval.length_eq sat₁, simp only at c, subst c,
    refl },
  sat_of_le := λ _ _ _ _, eval.of_le }

/- Note: The bitblast interface embeds the size of the vector. The SMT interface
   is untyped: this demotes the typed operators into untyped ones. -/
protected def demote_mk_binary_op (r : ℕ → ℕ) (f : ∀ {n : ℕ}, vector β n → vector β n → state γ (vector β (r n))) :
  (Σ (n : ℕ), vector β n) → (Σ (n : ℕ), vector β n) → state γ (Σ (n : ℕ), vector β n)
| ⟨n₁, x'⟩ ⟨n₂, y'⟩ :=
  if H : n₁ = n₂
  then f x' (H.symm.rec_on y') >>= λ x, pure (sigma.mk (r n₁) x)
  else pure default -- Dummy value if ill-typed

protected theorem increasing_demote_mk_binary_op {r : ℕ → ℕ} (f : ∀ {n : ℕ}, vector β n → vector β n → state γ (vector β (r n))) :
  (∀ (n : ℕ) (e₁ e₂ : vector β n), increasing (f e₁ e₂)) →
  ∀ (e₁ e₂ : Σ n, vector β n), increasing (sat.demote_mk_binary_op r @f e₁ e₂) :=
begin
  intros h e₁ e₂,
  cases e₁ with n₁ e₁,
  cases e₂ with n₂ e₂,
  simp only [sat.demote_mk_binary_op],
  split_ifs with h',
  { apply increasing_bind,
    { subst h',
      apply h },
    { intros, simp only [increasing_pure] } },
  { simp only [increasing_bind, increasing_pure] }
end

/-- Shift operations don't require both arguments to have the same widths. -/
protected def demote_mk_shift_op (f : ∀ {n₁ n₂ : ℕ}, vector β n₁ → vector β n₂ → state γ (vector β n₁)) :
  (Σ (n : ℕ), vector β n) → (Σ (n : ℕ), vector β n) → state γ (Σ (n : ℕ), vector β n)
| ⟨n₁, x'⟩ ⟨n₂, y'⟩ := sigma.mk n₁ <$> f x' y'

protected theorem increasing_demote_mk_shift_op (f : ∀ {n₁ n₂ : ℕ}, vector β n₁ → vector β n₂ → state γ (vector β n₁)) :
  (∀ {n₁ n₂ : ℕ} (e₁ : vector β n₁) (e₂ : vector β n₂), increasing (f e₁ e₂)) →
  ∀ (e₁ e₂ : Σ n, vector β n), increasing (sat.demote_mk_shift_op @f e₁ e₂) :=
begin
  intros h e₁ e₂,
  cases e₁ with n₁ e₁,
  cases e₂ with n₂ e₂,
  simp only [sat.demote_mk_shift_op],
  apply increasing_bind,
  { apply h },
  { apply increasing_pure }
end

end sat

section decision
variables {ω : Type*} (decider : sat.decision_procedure β γ ω)
include decider
open semidecision

def decide_via_reduce_to_sat : smt.decision_procedure (Σ n, vector β n) γ ω :=
begin
  rintros ⟨g, ⟨n₁, e⟩, ⟨n₂, v₂⟩⟩ w,
  refine bind_true (of_decidable (n₁ = n₂)) (λ h₁, _),
  refine bind_true (of_decidable (n₁ = 1)) (λ h₂, _),
  subst h₁, subst h₂,
  refine (decider (g, e.head, v₂ 0) w).modus_ponens _,
  simp only [factory.sat, sat.iff_eval],
  rintros h ⟨_, _⟩ ev,
  have c := eval.length_eq ev, simp only at c, subst c,
  congr,
  rw [eval.iff_singleton] at ev,
  ext i,
  rw [fin.eq_zero i, h _ ev]
end

end decision

section oracle
omit factory_instance
variables {β' ω' γ' : Type} (sat_oracle : sat.oracle β' γ' ω')

meta def reduce_to_sat_oracle : smt.oracle (Σ n, vector β' n) γ' ω' :=
λ ⟨g, ⟨r, b⟩⟩,
  match r, b with
  | ⟨1, r'⟩, ⟨1, b'⟩ := sat_oracle (g, (r'.head, (b' 0)))
  | _,        _      := tactic.fail "Can only create proofs for 1-bit bitvectors."
  end

end oracle

/-- Helper for creating a unary bitwise operator. -/
@[reducible]
def mk_unary_bitwise_op (f : β → state γ β) ⦃n : ℕ⦄ : vector β n → state γ (vector β n) :=
vector.mmap f

theorem le_mk_unary_bitwise_op {f : β → state γ β} (h : ∀ x, increasing (f x)) :
  ∀ {g : γ} {n : ℕ} (v : vector β n), g ≤ ((mk_unary_bitwise_op f v).run g).2 :=
λ _ _ _, increasing_vector_mmap _ _ h

@[reducible]
private def unary_op_spec (g₀ : γ) (f : β → state γ β) (f' : bool → bool) : Prop :=
∀ ⦃g g' : γ⦄ ⦃e₁ e₂ : β⦄ ⦃v₁ : bool⦄,
  g₀ ≤ g →
  (f e₁).run g = (e₂, g') →
  factory.sat g  e₁ v₁ →
  factory.sat g' e₂ (f' v₁)

theorem eval_mk_unary_bitwise_op
  {f : β → state γ β} {f' : bool → bool}
  (h_le : ∀ x, increasing (f x)) :
  ∀ {n : ℕ} {g g' : γ} {v₁ v₂ : vector β n} {b₁ : fin n → bool},
    unary_op_spec g f f' →
    (mk_unary_bitwise_op f v₁).run g = (v₂, g') →
    eval g v₁ b₁ →
    eval g' v₂ (λ i, f' (b₁ i))
| 0 g g' v₁ v₂ b₁ h := λ _ _, by {
  rw [vector.eq_nil v₂],
  apply list.forall₂.nil }
| (n + 1) g g' v₁ v₂ b₁ h := λ mk eval₁, by {
  simp only [mk_unary_bitwise_op, vector.mmap, state_t.run_bind, state_t.run_pure] at mk,
  simp only [has_bind.bind, id_bind, pure] at mk,
  cases mk,
  clear mk,
  apply eval.of_tail,
  { simp only [vector.cons_head],
    refine factory.sat_of_le (by apply le_mk_unary_bitwise_op h_le) _,
    refine h (le_refl g) (by rw [prod.mk.eta]) _,
    rw [eval.iff_head_tail] at eval₁,
    exact eval₁.1 },
  { simp only [fin.tail],
    apply eval_mk_unary_bitwise_op,
    { intros _ _ _ _ _ l mk sat₁,
      exact h (le_trans (h_le v₁.head) l) mk sat₁ },
    { simp only [prod.mk.eta, vector.cons_tail] },
    { rw [eval.iff_head_tail] at eval₁,
      exact eval.of_le (by apply h_le) eval₁.2 } } }

/-- Helper for creating a binary bitwise operator. -/
def mk_binary_bitwise_op (f : β → β → state γ β) :
  ∀ ⦃n : ℕ⦄ (v₁ v₂ : vector β n), state γ (vector β n)
| 0       _  _  := pure vector.nil
| (n + 1) v₁ v₂ := do
  t ← f v₁.head v₂.head,
  r ← @mk_binary_bitwise_op n (vector.tail v₁) (vector.tail v₂),
  pure $ t ::ᵥ r

theorem le_mk_binary_bitwise_op {f : β → β → state γ β} (h : ∀ x y, increasing (f x y))
  : ∀ {g : γ} {n : ℕ} (x y : vector β n),
  g ≤ ((mk_binary_bitwise_op f x y).run g).2
| _ 0       _ _ := by refl
| _ (n + 1) _ _ := by {
  simp only [mk_binary_bitwise_op],
  apply increasing_bind,
  apply h,
  intros,
  apply increasing_bind,
  intro,
  apply' le_mk_binary_bitwise_op,
  intros, apply increasing_pure }

@[reducible]
private def binary_op_spec (g₀ : γ) (f : β → β → state γ β) (f' : bool → bool → bool) : Prop :=
∀ ⦃g g' : γ⦄ ⦃e₁ e₂ e₃ : β⦄ ⦃v₁ v₂ : bool⦄,
  g₀ ≤ g →
  (f e₁ e₂).run g = (e₃, g') →
  factory.sat g  e₁ v₁ →
  factory.sat g  e₂ v₂ →
  factory.sat g' e₃ (f' v₁ v₂)

theorem eval_mk_binary_bitwise_op
  {f : β → β → state γ β} {f' : bool → bool → bool}
  (h_le : ∀ x y, increasing (f x y)) :
  ∀ {n : ℕ} {g g' : γ} {v₁ v₂ v₃ : vector β n} {b₁ b₂ : fin n → bool},
    binary_op_spec g f f' →
    (mk_binary_bitwise_op f v₁ v₂).run g = (v₃, g') →
    eval g v₁ b₁ →
    eval g v₂ b₂ →
    eval g' v₃ (λ i, f' (b₁ i) (b₂ i))
| 0 g g' v₁ v₂ v₃ b₁ b₂ h := λ _ _ _, by {
  rw [vector.eq_nil v₃],
  apply list.forall₂.nil }
| (n + 1) g g' v₁ v₂ v₃ b₁ b₂ h := λ mk eval₁ eval₂, by {
  simp only [mk_binary_bitwise_op, state_t.run_bind, state_t.run_pure] at mk,
  simp only [has_bind.bind, id_bind, pure] at mk,
  cases mk,
  clear mk,
  apply eval.of_tail,
  { simp only [vector.cons_head],
    refine factory.sat_of_le (by apply le_mk_binary_bitwise_op h_le) _,
    refine h (le_refl g) (by rw [prod.mk.eta]) _ _,
    { rw [eval.iff_head_tail] at eval₁,
      exact eval₁.1 },
    { rw [eval.iff_head_tail] at eval₂,
      exact eval₂.1 } },
  { simp only [fin.tail],
    apply eval_mk_binary_bitwise_op,
    { intros _ _ _ _ _ _ _ l mk sat₁ sat₂,
      exact h (le_trans (h_le v₁.head v₂.head) l) mk sat₁ sat₂ },
    { simp only [prod.mk.eta, vector.cons_tail],
      refl },
    { rw [eval.iff_head_tail] at eval₁,
      exact eval.of_le (by apply h_le) eval₁.2 },
    { rw [eval.iff_head_tail] at eval₂,
      exact eval.of_le (by apply h_le) eval₂.2 } } }

end bitblast
end smt
