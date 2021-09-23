/-
Copyright (c) 2021 The UNSAT Group. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luke Nelson, Xi Wang
-/
import tactic.apply
import tactic.basic

/-!
# Satisfiability

Basic properties of satisfiability.

## Implementation notes

* Import tactic.apply for tactics that fix the "apply bug" (e.g., refl').
-/

/-- Typeclass evaluating to Prop given an assignment. -/
class has_sat (α : out_param Type*) (β : Type*) :=
(sat : (α → bool) → β → Prop)

reserve infix ` ⊨ `:25
infix ⊨ := has_sat.sat

reserve infix ` ⊭ `:25
notation p ⊭ f := ¬ (p ⊨ f)

section
variables {α β β₁ β₂ β₃ : Type*}
          [has_sat α β] [has_sat α β₁] [has_sat α β₂] [has_sat α β₃]
include α

/-- f is unsatisfiable. -/
def unsatisfiable (f : β) : Prop :=
∀ (p : α → bool), ¬ (p ⊨ f)

lemma unsat_of_forall_exists {f₁ : β₁} {f₂ : β₂} (h : ∀ p₂, p₂ ⊨ f₂ → ∃ p₁, p₁ ⊨ f₁) :
  unsatisfiable f₁ → unsatisfiable f₂ :=
by { contrapose, simp [unsatisfiable], tauto }

namespace sat

/-- f₁ and f₂ are logically equivalent. -/
def liff (f₁ : β₁) (f₂ : β₂) : Prop :=
∀ (p : α → bool), p ⊨ f₁ ↔ p ⊨ f₂

reserve infix ` ⇔ `:50
infix ⇔ := liff

/-- f₁ logically implies f₂. -/
def limplies (f₁ : β₁) (f₂ : β₂) : Prop :=
∀ (p : α → bool), p ⊨ f₁ → p ⊨ f₂

reserve infixr ` ⇒ `:40
infixr ⇒ := limplies

@[refl]
protected lemma liff.refl (f : β) :
  f ⇔ f :=
by tauto

protected lemma liff.symm {f₁ : β₁} {f₂ : β₂} :
  f₁ ⇔ f₂ →
  f₂ ⇔ f₁ :=
by finish [liff]

@[symm]
protected lemma liff.symm' {f₁ f₂ : β} :
  f₁ ⇔ f₂ →
  f₂ ⇔ f₁ :=
@liff.symm _ _ _ _ _ f₁ f₂

protected lemma liff.trans {f₁ : β₁} {f₂ : β₂} {f₃ : β₃} :
  f₁ ⇔ f₂ →
  f₂ ⇔ f₃ →
  f₁ ⇔ f₃ :=
by finish [liff]

@[trans]
protected lemma liff.trans' {f₁ f₂ f₃ : β} :
  f₁ ⇔ f₂ →
  f₂ ⇔ f₃ →
  f₁ ⇔ f₃ :=
@liff.trans _ _ _ _ _ _ _ f₁ f₂ f₃

@[refl]
protected lemma limplies.refl (f : β) :
  f ⇒ f :=
by tauto

protected lemma limplies.trans {f₁ : β₁} {f₂ : β₂} {f₃ : β₃} :
  f₁ ⇒ f₂ →
  f₂ ⇒ f₃ →
  f₁ ⇒ f₃ :=
by tauto

@[trans]
protected lemma limplies.trans' {f₁ f₂ f₃ : β} :
  f₁ ⇒ f₂ →
  f₂ ⇒ f₃ →
  f₁ ⇒ f₃ :=
@limplies.trans _ _ _ _ _ _ _ f₁ f₂ f₃

lemma liff_iff_limplies_and_limplies {f₁ : β₁} {f₂ : β₂} :
  (f₁ ⇔ f₂) ↔ (f₁ ⇒ f₂) ∧ (f₂ ⇒ f₁) :=
begin
  split,
  { intro h,
    finish [liff, limplies] },
  { tauto }
end

lemma limplies_of_liff_left {f₁ : β₁} {f₂ : β₂} (h : f₁ ⇔ f₂) :
  f₁ ⇒ f₂ :=
(liff_iff_limplies_and_limplies.1 h).1

lemma limplies_of_liff_right {f₁ : β₁} {f₂ : β₂} (h : f₁ ⇔ f₂) :
  f₂ ⇒ f₁ :=
(liff_iff_limplies_and_limplies.1 h).2

lemma liff_unsat {f₁ : β₁} {f₂ : β₂} (h : f₁ ⇔ f₂) :
  unsatisfiable f₁ ↔ unsatisfiable f₂ :=
by finish [liff, unsatisfiable]

lemma limplies_unsat {f₁ : β₁} {f₂ : β₂} (h : f₂ ⇒ f₁) :
  unsatisfiable f₁ → unsatisfiable f₂ :=
by tauto

end sat

end
