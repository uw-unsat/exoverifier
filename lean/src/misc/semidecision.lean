/-
Copyright (c) 2021 The UNSAT Group. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luke Nelson, Xi Wang
-/
import tactic.basic

/-- Like `decidable` but with an "unknown" value. Useful, for example, when we don't care about completeness. -/
inductive semidecision (P : Prop) : Type
| is_true  :  P → semidecision
| is_false : ¬P → semidecision
| unknown  :      semidecision

namespace semidecision
variables {P Q : Prop}

instance : inhabited (semidecision P) := ⟨unknown⟩

protected def repr : semidecision P → string
| (is_true _)  := "is_true"
| (is_false _) := "is_false"
| unknown      := "unknown"

instance : has_repr (semidecision P) := ⟨semidecision.repr⟩

def of_decidable (P : Prop) : ∀ [decidable P], semidecision P
| (decidable.is_true h)  := is_true h
| (decidable.is_false h) := is_false h

/-- Convert semidecision to `tt` iff P is definitely true. -/
def to_bool : semidecision P → bool
| (is_true _) := tt
| _           := ff

def as_true : semidecision P → Prop
| (is_true _) := true
| _           := false

lemma of_as_true : ∀ (x : semidecision P), as_true x → P
| (is_true h)  _ := h
| (is_false _) h := h.elim
| unknown      h := h.elim

def as_false : semidecision P → Prop
| (is_false _) := true
| _            := false

lemma not_of_as_false : ∀ (x : semidecision P), as_false x → ¬P
| (is_true _)  h := h.elim
| (is_false h) _ := h
| unknown      h := h.elim

def negate : semidecision P → semidecision ¬P
| (is_true p)  := is_false (by tauto)
| (is_false p) := is_true (by tauto)
| unknown      := unknown

/-- Sequence two semidecisions, using the first one first.
    NB: it is not currently possible to define a `has_orelse` instance because the type of
    `has_orelse` is `(Type u_1 → Type u_2) → Type (max (u_1+1) u_2)`, and
    `semidecision` has type `Sort 0 → Sort 1`. -/
def orelse : semidecision P → semidecision P → semidecision P
| (is_true p)  := λ _, is_true p
| (is_false p) := λ _, is_false p
| _            := id

def bind_cases : semidecision P → (P → semidecision Q) → (¬P → semidecision Q) → semidecision Q
| (is_true p)  t _ := t p
| (is_false p) _ f := f p
| _            _ _ := unknown

/-- `bind` for semidecisions. Cannot instantiate `has_bind` for same reason as `has_orelse` above. -/
def bind_true : semidecision P → (P → semidecision Q) → semidecision Q :=
λ p t, bind_cases p t (λ _, unknown)

/-- Like bind, but takes a function of the negation of P. -/
def bind_false : semidecision P → (¬P → semidecision Q) → semidecision Q :=
λ p f, bind_cases p (λ _, unknown) f

/-- Convert a semidecision to a weaker semidecision using modus ponens. -/
def modus_ponens : semidecision P → (P → Q) → semidecision Q :=
λ p h, p.bind_true (is_true ∘ h)

/-- Convert a semidecision to a stronger semidecision using modus tollens. -/
def modus_tollens : semidecision Q → (P → Q) → semidecision P :=
λ p h, p.bind_false (λ nq, is_false (nq ∘ h))

/-- `decision_procedure L ω` is a procedure that semidecides, for a given x, whether x ∈ L
    using values of type ω as witnesses. -/
abbreviation procedure {α : Type*} (L : set α) (ω : Type*) : Type* :=
∀ (x : α), ω → semidecision (L x)

/-- An oracle is a (meta) function that generates witnesses from inputs.
    It can use unsafe Lean features, such as calling to an external SAT solver, for example. -/
meta abbreviation oracle (α ω : Type) : Type :=
α → tactic ω

/-- Get a witness for an input from an oracle with `exact`. -/
meta def by_oracle {α ω : Type} [has_reflect ω] [reflected ω] (o : oracle α ω) (x : α) : tactic unit := do
w : ω ← o x,
tactic.exact `(w : ω)

/- Helpers for decision procedures -/
namespace procedure

variables {α ω ω₁ ω₂ : Type*} -- Let α and ω be the the types of expressions and witnesses, respectively.
variables {L L₁ L₂ : set α} -- L is a language over α
variable (R : α → ω → Prop) -- R is a relation between α and ω

/-- R is sound w.r.t. L when, for any x, if there exists a w s.t. R x w then x ∈ L. -/
abbreviation sound : Prop :=
∀ x w, R x w → L x

/-- Make a decision procedure by showing the soundness of a decidable relation R : α → ω → Prop
    w.r.t. the language L. -/
def of_decidable_sound_relation [∀ x w, decidable (R x w)] (s : sound R) : procedure L ω :=
λ x w, (of_decidable _).modus_ponens $ s x w

/-- Make a complete decision procedure for the language if the language is decidable. -/
def of_decidable_language [decidable_pred L] : procedure L ω :=
λ x _, of_decidable _

def of_subset_procedure (f : procedure L₁ ω) (h : L₁ ⊆ L₂) : procedure L₂ ω :=
λ x w, (f x w).modus_ponens $ @h _

/-- Sequence two decision procedures. -/
def sequence (f : procedure L ω) (g : procedure L ω) : procedure L ω :=
λ x w, (f x w).orelse (g x w)

/-- Sequence two decision procedures with two (potentially different) witnesses. -/
def sequence' (f : procedure L ω₁) (g : procedure L ω₂) : procedure L (ω₁ × ω₂) :=
λ x w, (f x w.1).orelse (g x w.2)

/-- Conditionally choose a decision procedure based on which witness is present. -/
def split (f : procedure L ω₁) (g : procedure L ω₂) : procedure L (ω₁ ⊕ ω₂) :=
λ x w,
  match w with
  | sum.inl w₁ := f x w₁
  | sum.inr w₂ := g x w₂
  end

/-- A trivial decision procedure that rejects everything. -/
def trivial : procedure L ω :=
λ _ _, unknown

end procedure
end semidecision

notation `semidec_trivial` L := L.of_as_true (by triv)
