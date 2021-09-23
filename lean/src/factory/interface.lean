/-
Copyright (c) 2021 The UNSAT Group. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luke Nelson, Xi Wang
-/
import data.erased
import data.vector
import data.vector.basic
import misc.semidecision
import tactic.basic

/-- A factory provides a way of constructing expressions of type β which denote
    concrete values of type α. A factory is equipped with a preorder which preserves
    the denotations of expressions into values. -/
class factory (α : Type*) (β : Type*) (γ : Type*) extends preorder γ :=
(sat : γ → β → α → Prop)
(default : inhabited β)
(init_f : γ)
(denote : β → erased α)
(denote_sound : ∀ {g : γ} {e : β} {x : α},
  sat g e x →
  denote e = erased.mk x)
(sat_of_le : ∀ {g g' : γ} {x : β} {b : α},
  g ≤ g' →
  sat g x b →
  sat g' x b)

attribute [nolint dangerous_instance] factory.to_preorder

namespace factory
namespace trivial
variables {α : Type*} [inhabited α]

/-- Trivial preorder instance for punit. -/
instance : preorder punit :=
{ le       := eq,
  le_refl  := λ _, rfl,
  le_trans := λ _ _ _ h₁ h₂, h₂.rec_on (h₁.rec_on rfl) }

/-- A trivial instance of a factory using values themselves as expressions. -/
instance : factory α α punit :=
{ sat          := λ _, eq,
  default      := infer_instance,
  init_f       := punit.star,
  denote       := erased.mk,
  denote_sound := by { tauto },
  sat_of_le    := λ _ _ _ _ _ h, h }

/-- For the trivial instance, one can convert sat proof for one factory into sat proof
    for any other factory. -/
theorem sat_of_sat {g g' : punit} {e v : α} :
  sat g  e v →
  sat g' e v :=
begin
  rintros ⟨⟩,
  exact rfl
end

/-- Run a stateful computation over punit trivially. -/
abbreviation runtriv (f : state punit α) : α :=
(f.run punit.star).1

end trivial
end factory

namespace factory
variables {α β γ : Type*} [factory α β γ]

end factory

namespace factory
namespace monad
variables {γ : Type*} [preorder γ]

@[reducible]
def increasing {α : Type*} (s : state γ α) : Prop :=
∀ {g : γ}, g ≤ (s.run g).2

@[simp]
lemma increasing_bind {α β : Type*} (x : state γ α) (f : α → state γ β) :
  increasing x →
  (∀ (c : α), increasing (f c)) →
  increasing (x >>= f) :=
begin
  intros h₁ h₂ _,
  transitivity,
  { apply h₁ },
  { rw [state_t.run_bind],
    apply h₂ }
end

@[simp]
lemma increasing_pure {α : Type*} (x : α) :
  increasing (pure x : state γ α) :=
λ _, by refl

@[simp]
lemma increasing_map {α β : Type*} (x : state γ α) (f : α → β) :
  increasing x →
  increasing (f <$> x) :=
begin
  intro h,
  simp only [functor.map],
  apply increasing_bind,
  { apply @h },
  { intro c,
    apply increasing_pure }
end

@[simp]
lemma increasing_vector_mmap {α β : Type*} (f : α → state γ β) : ∀ {n : ℕ} (v : vector α n),
  (∀ x, increasing (f x)) →
  increasing (vector.mmap f v)
| 0       v :=
  by simp only [vector.eq_nil v, increasing_pure, implies_true_iff, vector.mmap_nil]
| (n + 1) v := by {
  rw [← vector.cons_head_tail v, vector.mmap_cons],
  intros h,
  apply increasing_bind,
  { tauto },
  intros c,
  apply increasing_bind,
  { tauto },
  simp }

end monad

/-- A factory decision procedure partially decides, for a given factory, expression and value `val₂`,
    whether if that expression has any value, then the expression must have value `val₂`.
    This somewhat odd phrasing leaves the decision procedure to ignore non-well-formed
    expressions: if the expression has no value, then the factory is free to return
    whatever decision. This imposes little to no burdern to the client of the decision factory,
    as one likely must prove the expression has a value anyways for it to be meaningful. -/
def decision_procedure (α : Type*) (β : Type*) (γ : Type*) [factory α β γ] (ω : Type*) :=
semidecision.procedure (λ e : (γ × β × α), ∀ v₂, sat e.1 e.2.1 v₂ → e.2.2 = v₂) ω

/-- An oracle for producing proofs / witnesses from expressions. -/
meta def oracle (α β γ ω : Type) : Type :=
semidecision.oracle (γ × β × α) ω

end factory
