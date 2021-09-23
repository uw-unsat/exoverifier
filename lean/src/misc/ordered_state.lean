/-
Copyright (c) 2021 The UNSAT Group. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luke Nelson, Xi Wang
-/
import order.lattice

structure ordered_state (γ : Type*) [preorder γ] (α : Type*) :=
  (run : Π (s : γ), α × { s' : γ // s ≤ s' })

namespace ordered_state

variables {γ : Type*} [preorder γ] {α β : Type*}

def pure (x : α) : ordered_state γ α :=
  ordered_state.mk (λ s, (x, ⟨s, by apply le_refl⟩))

def bind (x : ordered_state γ α) (f : α → ordered_state γ β) : ordered_state γ β :=
  ordered_state.mk $
    λ s, let (y, ⟨s', h1⟩) := x.run s,
             (z, ⟨s'', h2⟩) := (f y).run s'
         in  (z, ⟨s'', by apply le_trans h1 h2⟩)

instance : has_pure (ordered_state γ) :=
{ pure := @pure _ _ }

instance : has_bind (ordered_state γ) :=
{ bind := @bind _ _ }

def get : ordered_state γ γ :=
  ordered_state.mk $ λ s, (s, ⟨s, by apply le_refl⟩)

def modify (f : γ → γ) (h : ∀ (s : γ), s ≤ f s) : ordered_state γ unit :=
  ordered_state.mk $ λ s, ((), ⟨f s, h s⟩)

end ordered_state
