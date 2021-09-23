/-
Copyright (c) 2021 The UNSAT Group. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luke Nelson, Xi Wang
-/
import data.bv.all
import data.bv.basic
import data.bv.vector
import data.list.basic
import factory.interface
import misc.bool
import misc.eq
import misc.vector

/-!
# SMT Bitvector Interface

This file specifies the interface for constructing SMT expressions that evaluate to bitvectors.
Bitvector values are represented as (Σ n, fin n → bool), i.e., fin n → bool for some bitwidth n.
-/

universe u

namespace smt
open factory factory.monad

class factory (β γ : Type*) extends factory (Σ (n : ℕ), fin n → bool) β γ :=
(width : γ → β → ℕ) -- Compute width of an expression.
(width_sound : ∀ {g : γ} {e : β} {v : Σ n, fin n → bool},
  sat g e v → width g e = v.1)

/-- `factory.decision_procedure` specialized to bitvector values (i.e., Σ n, fin n → bool). -/
abbreviation decision_procedure (β γ : Type*) [factory β γ] (ω : Type*) : Type* :=
factory.decision_procedure (Σ (n : ℕ), fin n → bool) β γ ω

/-- `factory.oracle` specialized to bitvector values (i.e., Σ n, fin n → bool). -/
meta abbreviation oracle (β γ ω : Type) : Type :=
factory.oracle (Σ (n : ℕ), fin n → bool) β γ ω

/-- Typeclass for creating bitvector constants. -/
class const_factory (β : out_param Type*) (γ : Type*) [factory β γ] :=
(mk_const : ∀ {n : ℕ}, lsbvector n → state γ β)
(le_mk_const : ∀ {n : ℕ} {v : lsbvector n}, increasing (mk_const v))
(sat_mk_const : ∀ {g g' : γ} {n : ℕ} {c : lsbvector n} {e : β},
  (mk_const c).run g = (e, g') →
  sat g' e (sigma.mk n c.nth))

namespace const_factory
variables {β γ : Type u} [factory β γ] [const_factory β γ]
open factory

/-- Make a 1-bit constant. -/
def mk_const1 (b : bool) : state γ β :=
mk_const (b ::ᵥ vector.nil)

/-- Make the 1-bit constant `ff`. -/
def mk_false : state γ β := mk_const1 ff

/-- Make the 1-bit constant `tt`. -/
def mk_true : state γ β := mk_const1 tt

theorem sat_mk_const1 {g g' : γ} {b : bool} {e : β} :
  (mk_const1 b).run g = (e, g') →
  sat g' e (sigma.mk 1 (λ _, b) : Σ n, fin n → bool) :=
begin
  intros mk,
  simp only [mk_const1] at mk,
  convert (sat_mk_const mk),
  funext i,
  simp only [vector.nth_cons_nil]
end

theorem sat_mk_false {g g' : γ} {e : β} :
  mk_false.run g = (e, g') →
  sat g' e (sigma.mk 1 (λ _, ff) : Σ n, fin n → bool) :=
by apply sat_mk_const1

theorem sat_mk_true {g g' : γ} {e : β} :
  mk_true.run g = (e, g') →
  sat g' e (sigma.mk 1 (λ _, tt) : Σ n, fin n → bool) :=
by apply sat_mk_const1

end const_factory

/-- Typeclass for creating `concat` operators. -/
class concat_factory (β : out_param Type*) (γ : Type*) [factory β γ] :=
(mk_concat     : β → β → state γ β)
(le_mk_concat  : ∀ {e₁ e₂}, increasing (mk_concat e₁ e₂))
(sat_mk_concat : ∀ {g g' : γ} {e₁ e₂ e₃ : β} {n₁ n₂ : ℕ} {v₁ : fin n₁ → bool} {v₂ : fin n₂ → bool},
  (mk_concat e₁ e₂).run g = (e₃, g') →
  sat g  e₁ (sigma.mk n₁ v₁) →
  sat g  e₂ (sigma.mk n₂ v₂) →
  sat g' e₃ (sigma.mk (n₁ + n₂) (bv.concat v₁ v₂) : Σ n, fin n → bool))

/-- Typeclass for creating `extract` operators. -/
class extract_factory (β : out_param Type*) (γ : Type*) [factory β γ] :=
(mk_extract     : ℕ → ℕ → β → state γ β)
(le_mk_extract  : ∀ {upper lower : ℕ} {e : β}, increasing (mk_extract upper lower e))
(sat_mk_extract : ∀ {g g' : γ} {e₁ e₂ : β} {upper lower n : ℕ} {v₁ : fin n → bool},
  (mk_extract upper lower e₁).run g = (e₂, g') →
  sat g  e₁ (sigma.mk n v₁) →
  ∀ (h₁ : upper < n) (h₂ : lower ≤ upper),
  sat g' e₂ (sigma.mk (upper - lower + 1) (bv.extract upper lower h₁ h₂ v₁) : Σ n, fin n → bool))

/-- Typeclass for creating `msb` operators. -/
class msb_factory (β : out_param Type*) (γ : Type*) [factory β γ] :=
(mk_msb     : β → state γ β)
(le_mk_msb  : ∀ {e : β}, increasing (mk_msb e))
(sat_mk_msb : ∀ {g g' : γ} {e₁ e₂ : β} {n : ℕ} {v₁ : fin n → bool},
  (mk_msb e₁).run g = (e₂, g') →
  sat g  e₁ (sigma.mk n v₁) →
  sat g' e₂ (sigma.mk 1 (λ _, bv.msb v₁) : Σ n, fin n → bool))

namespace msb_default
variables {β γ : Type u} [factory β γ] [const_factory β γ] [extract_factory β γ]
open factory const_factory extract_factory

/-- Create an operator that extracts the most significant bit. -/
def mk_msb (e : β) : state γ β := do
g ← state_t.get,
let width : ℕ := factory.width g e in
match width with
| 0       := mk_false
| (n + 1) := mk_extract n n e
end

theorem le_mk_msb ⦃e : β⦄ (g : γ) :
  g ≤ ((mk_msb e).run g).2 :=
begin
  simp only [mk_msb, state_t.run_bind, state_t.run_get, is_lawful_monad.pure_bind],
  cases (factory.width g e),
  { apply le_mk_const },
  { apply le_mk_extract }
end

theorem sat_mk_msb ⦃g g' : γ⦄ {e₁ e₂ : β} {n : ℕ} {v₁ : fin n → bool} :
  (mk_msb e₁).run g = (e₂, g') →
  sat g e₁ (sigma.mk n v₁ : Σ n, fin n → bool) →
  sat g' e₂ (sigma.mk 1 (λ _, bv.msb v₁) : Σ n, fin n → bool) :=
begin
  intros mk sat₁,
  simp only [mk_msb, state_t.run_bind, state_t.run_get, is_lawful_monad.pure_bind, factory.width_sound sat₁] at mk,
  cases n; simp only [mk_msb] at mk,
  { apply sat_mk_false mk },
  { have sat₂ := sat_mk_extract mk sat₁ (by omega) (by omega),
    convert sat₂,
    { simp only [nat.sub_self] },
    { ext i; simp [bv.extract_msb] } }
end

@[priority 20]
instance : msb_factory β γ :=
{ mk_msb     := mk_msb,
  le_mk_msb  := le_mk_msb,
  sat_mk_msb := sat_mk_msb }

end msb_default

/-- Typeclass for creating bitvector variables. -/
class var_factory (β : out_param Type*) (γ : Type*) [factory β γ] :=
(mk_var : ∀ {n : ℕ}, erased (fin n → bool) → state γ β)
(le_mk_var : ∀ {n : ℕ} {v : erased (fin n → bool)}, increasing (mk_var v))
(sat_mk_var : ∀ {g g' : γ} {n : ℕ} {c} {e : β},
  (mk_var c).run g = (e, g') →
  sat g' e (⟨n, c.out⟩ : Σ n, fin n → bool))

/-- Typeclass for creating bitwise `not` operators. -/
class not_factory (β : out_param Type*) (γ : Type*) [factory β γ] :=
(mk_not      : β → state γ β)
(le_mk_not   : ∀ {e₁}, increasing (mk_not e₁))
(sat_mk_not  : ∀ {g g' : γ} {e₁ e₂ : β} {n : ℕ} {v₁ : fin n → bool},
  (mk_not e₁).run g = (e₂, g') →
  sat g  e₁ (sigma.mk n v₁) →
  sat g' e₂ (sigma.mk n (bv.not v₁)))

/-- Typeclass for creating bitwise `and` operators. -/
class and_factory (β : out_param Type*) (γ : Type*) [factory β γ] :=
(mk_and      : β → β → state γ β)
(le_mk_and   : ∀ {e₁ e₂}, increasing (mk_and e₁ e₂))
(sat_mk_and  : ∀ {g g' : γ} {e₁ e₂ e₃ : β} {n : ℕ} {v₁ v₂ : fin n → bool},
  (mk_and e₁ e₂).run g = (e₃, g') →
  sat g  e₁ (sigma.mk n v₁) →
  sat g  e₂ (sigma.mk n v₂) →
  sat g' e₃ (sigma.mk n (bv.and v₁ v₂)))

/-- Typeclass for creating bitwise `or` operators. -/
class or_factory (β : out_param Type*) (γ : Type*) [factory β γ] :=
(mk_or      : β → β → state γ β)
(le_mk_or   : ∀ {e₁ e₂}, increasing (mk_or e₁ e₂))
(sat_mk_or  : ∀ {g g' : γ} {e₁ e₂ e₃ : β} {n : ℕ} {v₁ v₂ : fin n → bool},
  (mk_or e₁ e₂).run g = (e₃, g') →
  sat g  e₁ (sigma.mk n v₁) →
  sat g  e₂ (sigma.mk n v₂) →
  sat g' e₃ (sigma.mk n (bv.or v₁ v₂)))

namespace or_default
variables {β γ : Type u} [factory β γ] [and_factory β γ] [not_factory β γ]
open and_factory not_factory

/-- Create a bitwise `or` operator. -/
def mk_or (e₁ e₂ : β) : state γ β := do
n_e₁ ← mk_not e₁,
n_e₂ ← mk_not e₂,
mk_and n_e₁ n_e₂ >>= mk_not

lemma le_mk_or ⦃e₁ e₂ : β⦄ (g : γ) :
  g ≤ ((mk_or e₁ e₂).run g).2 :=
begin
  simp only [mk_or],
  apply increasing_bind,
  apply le_mk_not,
  intros,
  apply increasing_bind,
  apply le_mk_not,
  intro c, apply increasing_bind,
  apply le_mk_and,
  intro c, apply le_mk_not
end

lemma sat_mk_or ⦃g g' : γ⦄ {e₁ e₂ e₃ : β} {n : ℕ} {v₁ v₂ : fin n → bool} :
  (mk_or e₁ e₂).run g = (e₃, g') →
  sat g e₁ (sigma.mk n v₁) →
  sat g e₂ (sigma.mk n v₂) →
  sat g' e₃ (sigma.mk n (bv.or v₁ v₂)) :=
begin
  intros mk sat₁ sat₂,
  simp only [mk_or, state_t.run_bind] at mk,
  convert_to _ using 0, swap,
  { apply sat_mk_not mk,
    apply sat_mk_and,
    by rw [prod.mk.eta],
    { exact sat_of_le le_mk_not (sat_mk_not (by rw [prod.mk.eta]) sat₁) },
    { exact sat_mk_not (by rw [prod.mk.eta]) (sat_of_le le_mk_not sat₂) } },
  congr, funext,
  simp only [bv.not, bv.and, bv.or, bool.bnot_band, bnot_bnot]
end

@[priority 20]
instance : or_factory β γ :=
{ mk_or     := mk_or,
  le_mk_or  := le_mk_or,
  sat_mk_or := sat_mk_or }

end or_default

/-- Typeclass for creating bitwise `xor` operators. -/
class xor_factory (β : out_param Type*) (γ : Type*) [factory β γ] :=
(mk_xor      : β → β → state γ β)
(le_mk_xor   : ∀ {e₁ e₂}, increasing (mk_xor e₁ e₂))
(sat_mk_xor  : ∀ {g g' : γ} {e₁ e₂ e₃ : β} {n : ℕ} {v₁ v₂ : fin n → bool},
  (mk_xor e₁ e₂).run g = (e₃, g') →
  sat g  e₁ (sigma.mk n v₁) →
  sat g  e₂ (sigma.mk n v₂) →
  sat g' e₃ (sigma.mk n (bv.xor v₁ v₂)))

namespace xor_default
variables {β γ : Type u} [factory β γ] [and_factory β γ] [or_factory β γ] [not_factory β γ]
open and_factory or_factory not_factory

/-- Create a bitwise `xor` operator. -/
def mk_xor (e₁ e₂ : β) : state γ β := do
n_e₁ ← mk_not e₁,
n_e₂ ← mk_not e₂,
e₁_n_e₂ ← mk_and e₁ n_e₂,
n_e₁_e₂ ← mk_and n_e₁ e₂,
mk_or e₁_n_e₂ n_e₁_e₂

lemma le_mk_xor ⦃e₁ e₂ : β⦄ (g : γ) :
  g ≤ ((mk_xor e₁ e₂).run g).2 :=
begin
  simp only [mk_xor],
  apply increasing_bind,
  apply le_mk_not,
  intro c, apply increasing_bind,
  apply le_mk_not,
  intro c, apply increasing_bind,
  apply le_mk_and,
  intro c, apply increasing_bind,
  apply le_mk_and,
  intro c, apply le_mk_or
end

lemma sat_mk_xor ⦃g g' : γ⦄ {e₁ e₂ e₃ : β} {n : ℕ} {v₁ v₂ : fin n → bool} :
  (mk_xor e₁ e₂).run g = (e₃, g') →
  sat g e₁ (sigma.mk n v₁) →
  sat g e₂ (sigma.mk n v₂) →
  sat g' e₃ (sigma.mk n (bv.xor v₁ v₂)) :=
begin
  intros mk sat₁ sat₂,
  simp only [mk_xor, state_t.run_bind] at mk,
  convert_to _ using 0, swap,
  { apply sat_mk_or mk,
    { apply sat_of_le le_mk_and,
      apply sat_mk_and, by rw [prod.mk.eta],
      { exact sat_of_le (le_trans le_mk_not le_mk_not) sat₁ },
      { apply sat_mk_not, by rw [prod.mk.eta],
        exact sat_of_le le_mk_not sat₂ } },
    { apply sat_mk_and, by rw [prod.mk.eta],
      { apply sat_of_le (le_trans le_mk_not le_mk_and),
        apply sat_mk_not, by rw [prod.mk.eta],
        exact sat₁ },
      { exact sat_of_le (le_trans (le_trans le_mk_not le_mk_not) le_mk_and) sat₂ } } },
  congr, funext,
  simp only [bv.not, bv.and, bv.or, bv.xor],
  cases (v₁ i); cases (v₂ i); refl
end

@[priority 20]
instance : xor_factory β γ :=
{ mk_xor     := mk_xor,
  le_mk_xor  := le_mk_xor,
  sat_mk_xor := sat_mk_xor }

end xor_default

/-- Typeclass for creating boolean `implies` operators. -/
class implies_factory (β : out_param Type*) (γ : Type*) [factory β γ] :=
(mk_implies      : β → β → state γ β)
(le_mk_implies   : ∀ {e₁ e₂}, increasing (mk_implies e₁ e₂))
(sat_mk_implies  : ∀ {g g' : γ} {e₁ e₂ e₃ : β} {v₁ v₂ : fin 1 → bool},
  (mk_implies e₁ e₂).run g = (e₃, g') →
  sat g  e₁ (sigma.mk 1 v₁ : Σ n, fin n → bool) →
  sat g  e₂ (sigma.mk 1 v₂ : Σ n, fin n → bool) →
  sat g' e₃ (sigma.mk 1 (λ _, bimplies (v₁ 0) (v₂ 0)) : Σ n, fin n → bool))

namespace implies_default
variables {β γ : Type u} [factory β γ] [or_factory β γ] [not_factory β γ]
open or_factory not_factory

/-- Create a bitwise implication operator. -/
def mk_implies (e₁ e₂ : β) : state γ β :=
mk_not e₁ >>= mk_or e₂

lemma le_mk_implies ⦃e₁ e₂ : β⦄ (g : γ) :
  g ≤ ((mk_implies e₁ e₂).run g).2 :=
begin
  simp only [mk_implies],
  apply increasing_bind,
  apply not_factory.le_mk_not,
  intros,
  apply or_factory.le_mk_or
end

lemma sat_mk_implies ⦃g g' : γ⦄ {e₁ e₂ e₃ : β} {v₁ v₂ : fin 1 → bool} :
  (mk_implies e₁ e₂).run g = (e₃, g') →
  sat g e₁ (sigma.mk 1 v₁ : Σ n, fin n → bool) →
  sat g e₂ (sigma.mk 1 v₂ : Σ n, fin n → bool) →
  sat g' e₃ (sigma.mk 1 (λ _, bimplies (v₁ 0) (v₂ 0)) : Σ n, fin n → bool) :=
begin
  intros mk sat₁ sat₂,
  simp only [bimplies_eq_bnot_bor],
  simp only [mk_implies, state_t.run_bind] at mk,
  simp only [has_bind.bind, id_bind] at mk,
  simp_rw [bool.bor_comm],
  apply sat_mk_or mk,
  change v₁ with (λ i, v₁ i) at sat₁,
  { convert (sat_of_le le_mk_not sat₂),
    funext, congr },
  { convert (sat_mk_not (by rw [prod.mk.eta]) sat₁),
    funext, congr }
end

@[priority 20]
instance : implies_factory β γ :=
{ mk_implies     := mk_implies,
  le_mk_implies  := le_mk_implies,
  sat_mk_implies := sat_mk_implies }

end implies_default

/-- Typeclass for creating arithmetic `add` operators. -/
class add_factory (β : out_param Type*) (γ : Type*) [factory β γ] :=
(mk_add      : β → β → state γ β)
(le_mk_add   : ∀ {e₁ e₂}, increasing (mk_add e₁ e₂))
(sat_mk_add  : ∀ {g g' : γ} {e₁ e₂ e₃ : β} {n : ℕ} {v₁ v₂ : fin n → bool},
  (mk_add e₁ e₂).run g = (e₃, g') →
  sat g  e₁ (sigma.mk n v₁) →
  sat g  e₂ (sigma.mk n v₂) →
  sat g' e₃ (sigma.mk n (v₁ + v₂)))

/-- Typeclass for creating arithmetic `neg` operators. -/
class neg_factory (β : out_param Type*) (γ : Type*) [factory β γ] :=
(mk_neg      : β → state γ β)
(le_mk_neg   : ∀ {e}, increasing (mk_neg e))
(sat_mk_neg  : ∀ {g g' : γ} {e e' : β} {n : ℕ} {v : fin n → bool},
  (mk_neg e).run g = (e', g') →
  sat g e (sigma.mk n v) →
  sat g' e' (sigma.mk n (-v)))

namespace neg_default
variables {β γ : Type u} [factory β γ] [const_factory β γ] [not_factory β γ] [add_factory β γ]
open factory const_factory not_factory add_factory

/-- Create a negation operator -/
def mk_neg (e₁ : β) : state γ β := do
g ← state_t.get,
let width : ℕ := factory.width g e₁ in do
not_e₁ ← mk_not e₁,
one ← mk_const $ vector.of_fn (1 : fin width → bool),
mk_add not_e₁ one

lemma le_mk_neg ⦃e₁ : β⦄ (g : γ) :
  g ≤ ((mk_neg e₁).run g).2 :=
begin
  simp only [mk_neg],
  apply increasing_bind,
  { intros r, refl },
  intros c,
  apply increasing_bind,
  apply le_mk_not,
  intro, apply increasing_bind,
  apply le_mk_const,
  intro, apply le_mk_add
end

lemma sat_mk_neg ⦃g g' : γ⦄ {e₁ e₂ : β} {n : ℕ} {v₁ : fin n → bool} :
  (mk_neg e₁).run g = (e₂, g') →
  sat g  e₁ (sigma.mk n v₁) →
  sat g' e₂ (sigma.mk n (-v₁)) :=
begin
  intros mk sat₁,
  simp only [mk_neg, state_t.run_bind, state_t.run_get, is_lawful_monad.pure_bind, factory.width_sound sat₁] at mk,
  have h := factory.width_sound sat₁, simp only at h, subst h,
  convert_to _ using 0, swap,
  { apply sat_mk_add mk,
    { apply sat_of_le le_mk_const,
      exact sat_mk_not (by rw [prod.mk.eta]) sat₁ },
    { exact sat_mk_const (by rw [prod.mk.eta]) } },
  rw [bv.neg_eq_not_add_one],
  congr,
  ext,
  simp only [vector.nth_of_fn]
end

@[priority 20]
instance : neg_factory β γ :=
{ mk_neg     := mk_neg,
  le_mk_neg  := le_mk_neg,
  sat_mk_neg := sat_mk_neg }

end neg_default

/-- Typeclass for creating arithmetic `sub` operators. -/
class sub_factory (β : out_param Type*) (γ : Type*) [factory β γ] :=
(mk_sub      : β → β → state γ β)
(le_mk_sub   : ∀ {e₁ e₂}, increasing (mk_sub e₁ e₂))
(sat_mk_sub  : ∀ {g g' : γ} {e₁ e₂ e₃ : β} {n : ℕ} {v₁ v₂ : fin n → bool},
  (mk_sub e₁ e₂).run g = (e₃, g') →
  sat g  e₁ (sigma.mk n v₁) →
  sat g  e₂ (sigma.mk n v₂) →
  sat g' e₃ (sigma.mk n (v₁ - v₂)))

namespace sub_default
variables {β γ : Type u} [factory β γ] [neg_factory β γ] [add_factory β γ]
open factory neg_factory add_factory

/-- Create a subtraction operator. -/
def mk_sub (e₁ e₂ : β) : state γ β :=
mk_neg e₂ >>= mk_add e₁

lemma le_mk_sub ⦃e₁ e₂ : β⦄ (g : γ) :
  g ≤ ((mk_sub e₁ e₂).run g).2 :=
begin
  simp only [mk_sub],
  apply increasing_bind,
  apply le_mk_neg,
  intros,
  apply le_mk_add
end

lemma sat_mk_sub ⦃g g' : γ⦄ {e₁ e₂ e₃ : β} {n : ℕ} {v₁ v₂ : fin n → bool} :
  (mk_sub e₁ e₂).run g = (e₃, g') →
  sat g e₁ (sigma.mk n v₁) →
  sat g e₂ (sigma.mk n v₂) →
  sat g' e₃ (sigma.mk n (v₁ - v₂)) :=
begin
  intros mk sat₁ sat₂,
  simp only [mk_sub, state_t.run_bind] at mk,
  simp only [has_bind.bind, id_bind] at mk,
  change v₁ - v₂ with v₁ + (-v₂),
  apply sat_mk_add mk,
  { exact sat_of_le le_mk_neg sat₁ },
  { exact sat_mk_neg (by rw [prod.mk.eta]) sat₂ },
end

@[priority 20]
instance : sub_factory β γ :=
{ mk_sub     := mk_sub,
  le_mk_sub  := le_mk_sub,
  sat_mk_sub := sat_mk_sub }

end sub_default

/-- Typeclass for creating arithmetic `udiv` operators. -/
class udiv_factory (β : out_param Type*) (γ : Type*) [factory β γ] :=
(mk_udiv      : β → β → state γ β)
(le_mk_udiv   : ∀ {e₁ e₂}, increasing (mk_udiv e₁ e₂))
(sat_mk_udiv  : ∀ {g g' : γ} {e₁ e₂ e₃ : β} {n : ℕ} {v₁ v₂ : fin n → bool},
  (mk_udiv e₁ e₂).run g = (e₃, g') →
  sat g  e₁ (sigma.mk n v₁) →
  sat g  e₂ (sigma.mk n v₂) →
  sat g' e₃ (sigma.mk n (v₁ / v₂)))

namespace udiv_default
variables {β γ : Type u} [factory β γ] [var_factory β γ]
open var_factory

/-- Create an unsigned division operator. -/
def mk_udiv (e₁ e₂ : β) : state γ β := do
g ← state_t.get,
mk_var $ do
  l ← (denote γ e₁ : erased Σ n, fin n → bool),
  r ← (denote γ e₂ : erased Σ n, fin n → bool),
  (by {
    cases l with n₁ v₁,
    cases r with n₂ v₂,
    by_cases h : (n₁ = (factory.width g e₁) ∧ n₁ = n₂),
    { obtain ⟨a, b⟩ := h, subst a, subst b,
      exact erased.mk (v₁ / v₂) },
    { exact erased.mk (λ _, ff) } } )

lemma le_mk_udiv ⦃e₁ e₂ : β⦄ (g : γ) :
  g ≤ ((mk_udiv e₁ e₂).run g).2 :=
begin
  simp only [mk_udiv],
  cases (denote γ e₁),
  cases (denote γ e₂),
  apply le_mk_var
end

lemma sat_mk_udiv ⦃g g' : γ⦄ {e₁ e₂ e₃ : β} {n : ℕ} {v₁ v₂ : fin n → bool} :
  (mk_udiv e₁ e₂).run g = (e₃, g') →
  sat g  e₁ (sigma.mk n v₁) →
  sat g  e₂ (sigma.mk n v₂) →
  sat g' e₃ (sigma.mk n (bv.udiv v₁ v₂)) :=
begin
  intros mk sat₁ sat₂,
  simp only [mk_udiv, state_t.run_bind, state_t.run_get, is_lawful_monad.pure_bind] at mk,
  rw [denote_sound sat₁, denote_sound sat₂] at mk,
  have h := factory.width_sound sat₁, simp only at h, subst h,
  convert (sat_mk_var mk); clear mk,
  { simp only [erased.bind_def, erased.bind_eq_out, erased.mk_out, erased.out_mk],
    rw [erased.out_mk, erased.out_mk],
    simp only,
    rw [dif_pos], swap,
    exact ⟨rfl, rfl⟩,
    simp only,
    rw [erased.out_mk],
    refl }
end

@[priority 20]
instance : udiv_factory β γ :=
{ mk_udiv     := mk_udiv,
  le_mk_udiv  := le_mk_udiv,
  sat_mk_udiv := sat_mk_udiv }

end udiv_default

/-- Typeclass for creating arithmetic `mul` operators. -/
class mul_factory (β : out_param Type*) (γ : Type*) [factory β γ] :=
(mk_mul      : β → β → state γ β)
(le_mk_mul   : ∀ {e₁ e₂}, increasing (mk_mul e₁ e₂))
(sat_mk_mul  : ∀ {g g' : γ} {e₁ e₂ e₃ : β} {n : ℕ} {v₁ v₂ : fin n → bool},
  (mk_mul e₁ e₂).run g = (e₃, g') →
  sat g  e₁ (sigma.mk n v₁) →
  sat g  e₂ (sigma.mk n v₂) →
  sat g' e₃ (sigma.mk n (v₁ * v₂)))

/-- Typeclass for creating arithmetic `urem` operators. -/
class urem_factory (β : out_param Type*) (γ : Type*) [factory β γ] :=
(mk_urem      : β → β → state γ β)
(le_mk_urem   : ∀ {e₁ e₂}, increasing (mk_urem e₁ e₂))
(sat_mk_urem  : ∀ {g g' : γ} {e₁ e₂ e₃ : β} {n : ℕ} {v₁ v₂ : fin n → bool},
  (mk_urem e₁ e₂).run g = (e₃, g') →
  sat g  e₁ (sigma.mk n v₁) →
  sat g  e₂ (sigma.mk n v₂) →
  sat g' e₃ (sigma.mk n (bv.urem v₁ v₂)))

/-- Typeclass for creating relational `eq` operators. -/
class eq_factory (β : out_param Type*) (γ : Type*) [factory β γ] :=
(mk_eq      : β → β → state γ β)
(le_mk_eq   : ∀ {e₁ e₂}, increasing (mk_eq e₁ e₂))
(sat_mk_eq  : ∀ {g g' : γ} {e₁ e₂ e₃ : β} {n : ℕ} {v₁ v₂ : fin n → bool},
  (mk_eq e₁ e₂).run g = (e₃, g') →
  sat g  e₁ (sigma.mk n v₁) →
  sat g  e₂ (sigma.mk n v₂) →
  sat g' e₃ (sigma.mk 1 (λ _, to_bool (v₁ = v₂)) : (Σ n, fin n → bool)))

/-- Typeclass for relational `ult` operators. -/
class ult_factory (β : out_param Type*) (γ : Type*) [factory β γ] :=
(mk_ult      : β → β → state γ β)
(le_mk_ult   : ∀ {e₁ e₂}, increasing (mk_ult e₁ e₂))
(sat_mk_ult  : ∀ {g g' : γ} {e₁ e₂ e₃ : β} {n : ℕ} {v₁ v₂ : fin n → bool},
  (mk_ult e₁ e₂).run g = (e₃, g') →
  sat g  e₁ (sigma.mk n v₁) →
  sat g  e₂ (sigma.mk n v₂) →
  sat g' e₃ ((sigma.mk 1 (λ _, to_bool (v₁ < v₂)) : Σ n, fin n → bool)))

/-- Typeclass for relational `ule` operators. -/
class ule_factory (β : out_param Type*) (γ : Type*) [factory β γ] :=
(mk_ule      : β → β → state γ β)
(le_mk_ule   : ∀ {e₁ e₂}, increasing (mk_ule e₁ e₂))
(sat_mk_ule  : ∀ {g g' : γ} {e₁ e₂ e₃ : β} {n : ℕ} {v₁ v₂ : fin n → bool},
  (mk_ule e₁ e₂).run g = (e₃, g') →
  sat g  e₁ (sigma.mk n v₁) →
  sat g  e₂ (sigma.mk n v₂) →
  sat g' e₃ ((sigma.mk 1 (λ _, to_bool (v₁ ≤ v₂)) : Σ n, fin n → bool)))

namespace ule_default
variables {β γ : Type u} [factory β γ] [not_factory β γ] [ult_factory β γ]
open factory not_factory ult_factory

/-- Create an unsigned less than or equal operator. -/
def mk_ule (e₁ e₂ : β) : state γ β :=
mk_ult e₂ e₁ >>= mk_not

lemma le_mk_ule ⦃e₁ e₂ : β⦄ (g : γ) :
  g ≤ ((mk_ule e₁ e₂).run g).2 :=
begin
  simp only [mk_ule],
  apply increasing_bind,
  apply le_mk_ult,
  apply le_mk_not
end

lemma sat_mk_ule ⦃g g' : γ⦄ {e₁ e₂ e₃ : β} {n : ℕ} {v₁ v₂ : fin n → bool} :
  (mk_ule e₁ e₂).run g = (e₃, g') →
  sat g  e₁ (sigma.mk n v₁) →
  sat g  e₂ (sigma.mk n v₂) →
  sat g' e₃ ((sigma.mk 1 (λ _, to_bool (v₁ ≤ v₂)) : Σ n, fin n → bool)) :=
begin
  intros mk sat₁ sat₂,
  simp only [mk_ule, state_t.run_bind] at mk,
  have h : (λ _ : fin 1, to_bool (v₁ ≤ v₂)) = bv.not (λ _ : fin 1, to_bool (v₂ < v₁)),
  { simp only [bv.not, ← not_lt],
    by_cases hlt : v₂ < v₁; simp [hlt] },
  rw h, clear h,
  apply sat_mk_not mk,
  apply sat_mk_ult,
  by rw [prod.mk.eta],
  from sat₂,
  from sat₁
end

@[priority 20]
instance : ule_factory β γ :=
{ mk_ule     := mk_ule,
  le_mk_ule  := le_mk_ule,
  sat_mk_ule := sat_mk_ule }

end ule_default

/-- Typeclass for relational `slt` operators. -/
class slt_factory (β : out_param Type*) (γ : Type*) [factory β γ] :=
(mk_slt      : β → β → state γ β)
(le_mk_slt   : ∀ {e₁ e₂}, increasing (mk_slt e₁ e₂))
(sat_mk_slt  : ∀ {g g' : γ} {e₁ e₂ e₃ : β} {n : ℕ} {v₁ v₂ : fin n → bool},
  (mk_slt e₁ e₂).run g = (e₃, g') →
  sat g  e₁ (sigma.mk n v₁ : Σ n, fin n → bool) →
  sat g  e₂ (sigma.mk n v₂ : Σ n, fin n → bool) →
  sat g' e₃ ((sigma.mk 1 (λ _, to_bool (bv.slt v₁ v₂)) : Σ n, fin n → bool)))

namespace slt_default
variables {β γ : Type u} [factory β γ] [ult_factory β γ] [msb_factory β γ] [or_factory β γ]
                         [and_factory β γ] [eq_factory β γ] [not_factory β γ]
open factory ult_factory msb_factory or_factory and_factory eq_factory not_factory

/-- Create a signed less than operator. -/
def mk_slt (e₁ e₂ : β) : state γ β := do
ult ← mk_ult e₁ e₂,
msb_v₁ ← mk_msb e₁,
msb_v₂ ← mk_msb e₂,
msb_match ← mk_eq msb_v₁ msb_v₂,
msb_match_ult ← mk_and msb_match ult,
n_msb_v₂ ← mk_not msb_v₂,
msb_lt ← mk_and msb_v₁ n_msb_v₂,
mk_or msb_lt msb_match_ult

lemma le_mk_slt ⦃e₁ e₂ : β⦄ (g : γ) :
  g ≤ ((mk_slt e₁ e₂).run g).2 :=
begin
  simp only [mk_slt],
  apply increasing_bind,
  apply le_mk_ult,
  intro c, apply increasing_bind,
  apply le_mk_msb,
  intro c, apply increasing_bind,
  apply le_mk_msb,
  intro c, apply increasing_bind,
  apply le_mk_eq,
  intro c, apply increasing_bind,
  apply le_mk_and,
  intro c, apply increasing_bind,
  apply le_mk_not,
  intro c, apply increasing_bind,
  apply le_mk_and,
  intro c, apply le_mk_or
end

lemma sat_mk_slt ⦃g g' : γ⦄ {e₁ e₂ e₃ : β} {n : ℕ} {v₁ v₂ : fin n → bool} :
  (mk_slt e₁ e₂).run g = (e₃, g') →
  sat g  e₁ (sigma.mk n v₁ : Σ n, fin n → bool) →
  sat g  e₂ (sigma.mk n v₂ : Σ n, fin n → bool) →
  sat g' e₃ ((sigma.mk 1 (λ _, to_bool (bv.slt v₁ v₂)) : Σ n, fin n → bool)) :=
begin
  intros mk sat₁ sat₂,
  simp only [mk_slt, denote_sound sat₁, state_t.run_bind] at mk,
  convert_to _ using 0, swap,
  { apply sat_mk_or mk; clear mk,
    { apply sat_mk_and,
      by rw [prod.mk.eta],
      { apply sat_of_le (le_trans (le_trans le_mk_msb le_mk_eq) (le_trans le_mk_and le_mk_not)),
        apply sat_mk_msb,
        by rw [prod.mk.eta],
        exact sat_of_le le_mk_ult sat₁ },
      { apply sat_mk_not,
        by rw [prod.mk.eta],
        apply sat_of_le (le_trans le_mk_eq le_mk_and),
        apply sat_mk_msb,
        by rw [prod.mk.eta],
        exact sat_of_le (le_trans le_mk_ult le_mk_msb) sat₂ } },
    { apply sat_of_le (le_trans le_mk_not le_mk_and),
      apply sat_mk_and,
      by rw [prod.mk.eta],
      { apply sat_mk_eq,
        by rw [prod.mk.eta],
        { apply sat_of_le le_mk_msb,
          apply sat_mk_msb,
          by rw [prod.mk.eta],
          exact sat_of_le le_mk_ult sat₁ },
        { apply sat_mk_msb,
          by rw [prod.mk.eta],
          exact sat_of_le (le_trans le_mk_ult le_mk_msb) sat₂ } },
      { apply sat_of_le (le_trans (le_trans le_mk_msb le_mk_msb) le_mk_eq),
        apply sat_mk_ult,
        by rw [prod.mk.eta],
        from sat₁,
        from sat₂ } } },
  clear mk,
  congr, funext i,
  simp only [bv.slt, bool.to_bool_and, bool.to_bool_or],
  cases bv.msb v₁; cases bv.msb v₂; refl
end

@[priority 20]
instance : slt_factory β γ :=
{ mk_slt     := mk_slt,
  le_mk_slt  := le_mk_slt,
  sat_mk_slt := sat_mk_slt }

end slt_default

/-- Typeclass for relational `sle` operators. -/
class sle_factory (β : out_param Type*) (γ : Type*) [factory β γ] :=
(mk_sle      : β → β → state γ β)
(le_mk_sle   : ∀ {e₁ e₂}, increasing (mk_sle e₁ e₂))
(sat_mk_sle  : ∀ {g g' : γ} {e₁ e₂ e₃ : β} {n : ℕ} {v₁ v₂ : fin n → bool},
  (mk_sle e₁ e₂).run g = (e₃, g') →
  sat g  e₁ (sigma.mk n v₁ : Σ n, fin n → bool) →
  sat g  e₂ (sigma.mk n v₂ : Σ n, fin n → bool) →
  sat g' e₃ ((sigma.mk 1 (λ _, to_bool (bv.sle v₁ v₂)) : Σ n, fin n → bool)))

namespace sle_default
variables {β γ : Type u} [factory β γ] [not_factory β γ] [slt_factory β γ]
open factory not_factory slt_factory

/-- Create a signed less than or equal operator. -/
def mk_sle (e₁ e₂ : β) : state γ β := do
mk_slt e₂ e₁ >>= mk_not

lemma le_mk_sle ⦃e₁ e₂ : β⦄ (g : γ) :
  g ≤ ((mk_sle e₁ e₂).run g).2 :=
begin
  simp only [mk_sle],
  apply increasing_bind,
  apply le_mk_slt,
  apply le_mk_not
end

lemma sat_mk_sle ⦃g g' : γ⦄ {e₁ e₂ e₃ : β} {n : ℕ} {v₁ v₂ : fin n → bool} :
  (mk_sle e₁ e₂).run g = (e₃, g') →
  sat g  e₁ (sigma.mk n v₁ : Σ n, fin n → bool) →
  sat g  e₂ (sigma.mk n v₂ : Σ n, fin n → bool) →
  sat g' e₃ ((sigma.mk 1 (λ _, to_bool (bv.sle v₁ v₂)) : Σ n, fin n → bool)) :=
begin
  intros mk sat₁ sat₂,
  simp only [mk_sle, state_t.run_bind] at mk,
  have h : (λ _ : fin 1, to_bool (bv.sle v₁ v₂)) = bv.not (λ _ : fin 1, to_bool (bv.slt v₂ v₁)),
  { simp only [bv.not, ← bv.not_slt],
    by_cases hlt : bv.slt v₂ v₁; simp [hlt] },
  rw h, clear h,
  apply sat_mk_not mk,
  apply sat_mk_slt,
  by rw [prod.mk.eta],
  from sat₂,
  from sat₁
end

@[priority 20]
instance : sle_factory β γ :=
{ mk_sle     := mk_sle,
  le_mk_sle  := le_mk_sle,
  sat_mk_sle := sat_mk_sle }

end sle_default

/-- Typeclass for creating conditional `ite` operators. -/
class ite_factory (β : out_param Type*) (γ : Type*) [factory β γ] :=
(mk_ite      : β → β → β → state γ β)
(le_mk_ite   : ∀ {e₁ e₂ e₃}, increasing (mk_ite e₁ e₂ e₃))
(sat_mk_ite  : ∀ {g g' : γ} {e₁ e₂ e₃ e₄ : β} {n : ℕ} {v₁ : fin 1 → bool} {v₂ v₃ : fin n → bool},
  (mk_ite e₁ e₂ e₃).run g = (e₄, g') →
  sat g  e₁ (sigma.mk 1 v₁ : Σ n, fin n → bool) →
  sat g  e₂ (sigma.mk n v₂) →
  sat g  e₃ (sigma.mk n v₃) →
  sat g' e₄ (sigma.mk n (bv.ite v₁ v₂ v₃)))

/-- Typeclass for creating shift `shl` operators. -/
class shl_factory (β : out_param Type*) (γ : Type*) [factory β γ] :=
(mk_shl      : β → β → state γ β)
(le_mk_shl   : ∀ {e₁ e₂}, increasing (mk_shl e₁ e₂))
(sat_mk_shl  : ∀ {g g' : γ} {e₁ e₂ e₃ : β} {n₁ n₂ : ℕ} {v₁ : fin n₁ → bool} {v₂ : fin n₂ → bool},
  (mk_shl e₁ e₂).run g = (e₃, g') →
  sat g  e₁ (⟨n₁, v₁⟩ : Σ n, fin n → bool) →
  sat g  e₂ (sigma.mk n₂ v₂) →
  sat g' e₃ (⟨n₁, bv.shl v₁ v₂⟩ : Σ n, fin n → bool))

/-- Typeclass for creating shift `lshr` operators. -/
class lshr_factory (β : out_param Type*) (γ : Type*) [factory β γ] :=
(mk_lshr      : β → β → state γ β)
(le_mk_lshr   : ∀ {e₁ e₂}, increasing (mk_lshr e₁ e₂))
(sat_mk_lshr  : ∀ {g g' : γ} {e₁ e₂ e₃ : β} {n₁ n₂ : ℕ} {v₁ : fin n₁ → bool} {v₂ : fin n₂ → bool},
  (mk_lshr e₁ e₂).run g = (e₃, g') →
  sat g  e₁ (⟨n₁, v₁⟩ : Σ n, fin n → bool) →
  sat g  e₂ (sigma.mk n₂ v₂) →
  sat g' e₃ (⟨n₁, bv.lshr v₁ v₂⟩ : Σ n, fin n → bool))

/-- Typeclass for creating shift `ashr` operators. -/
class ashr_factory (β : out_param Type*) (γ : Type*) [factory β γ] :=
(mk_ashr      : β → β → state γ β)
(le_mk_ashr   : ∀ {e₁ e₂}, increasing (mk_ashr e₁ e₂))
(sat_mk_ashr  : ∀ {g g' : γ} {e₁ e₂ e₃ : β} {n₁ n₂ : ℕ} {v₁ : fin n₁ → bool} {v₂ : fin n₂ → bool},
  (mk_ashr e₁ e₂).run g = (e₃, g') →
  sat g  e₁ (⟨n₁, v₁⟩ : Σ n, fin n → bool) →
  sat g  e₂ (sigma.mk n₂ v₂) →
  sat g' e₃ (⟨n₁, bv.ashr v₁ v₂⟩ : Σ n, fin n → bool))

namespace ashr_default
variables {β γ : Type u} [factory β γ] [not_factory β γ] [msb_factory β γ] [lshr_factory β γ]
                         [ite_factory β γ]
open factory not_factory msb_factory lshr_factory ite_factory

/-- Create an `ashr` operator. -/
def mk_ashr (e₁ e₂ : β) : state γ β := do
n_e₁ ← mk_not e₁,
r₁ ← mk_lshr n_e₁ e₂ >>= mk_not,
r₂ ← mk_lshr e₁ e₂,
msb₁ ← mk_msb e₁,
mk_ite msb₁ r₁ r₂

lemma le_mk_ashr ⦃e₁ e₂ : β⦄ (g : γ) :
  g ≤ ((mk_ashr e₁ e₂).run g).2 :=
begin
  simp only [mk_ashr],
  apply increasing_bind,
  apply le_mk_not,
  intro, apply increasing_bind,
  { apply increasing_bind,
    apply le_mk_lshr,
    apply le_mk_not },
  intro, apply increasing_bind,
  apply le_mk_lshr,
  intro, apply increasing_bind,
  apply le_mk_msb,
  intro, apply le_mk_ite
end

lemma sat_mk_ashr ⦃g g' : γ⦄ {e₁ e₂ e₃ : β} {n₁ n₂ : ℕ} {v₁ : fin n₁ → bool} {v₂ : fin n₂ → bool} :
  (mk_ashr e₁ e₂).run g = (e₃, g') →
  sat g  e₁ (⟨n₁, v₁⟩ : Σ n, fin n → bool) →
  sat g  e₂ (sigma.mk n₂ v₂) →
  sat g' e₃ (⟨n₁, bv.ashr v₁ v₂⟩ : Σ n, fin n → bool) :=
begin
  intros mk sat₁ sat₂,
  simp only [mk_ashr, state_t.run_bind] at mk,
  simp only [has_bind.bind, id_bind] at mk,
  convert_to _ using 0, clear mk, swap,
  { apply sat_mk_ite mk; clear mk,
    { apply sat_mk_msb, by rw [prod.mk.eta],
      exact sat_of_le (le_trans (le_trans (le_trans le_mk_not le_mk_lshr) le_mk_not) le_mk_lshr) sat₁ },
    { apply sat_of_le (le_trans le_mk_lshr le_mk_msb),
      apply sat_mk_not, by rw [prod.mk.eta],
      apply sat_mk_lshr, by rw [prod.mk.eta],
      { exact sat_mk_not (by rw [prod.mk.eta]) sat₁ },
      { exact sat_of_le le_mk_not sat₂ } },
    { apply sat_of_le le_mk_msb,
      apply sat_mk_lshr, by rw [prod.mk.eta],
      { exact sat_of_le (le_trans (le_trans le_mk_not le_mk_lshr) le_mk_not) sat₁ },
      { exact sat_of_le (le_trans (le_trans le_mk_not le_mk_lshr) le_mk_not) sat₂ } } },
  congr
end

@[priority 20]
instance : ashr_factory β γ :=
{ mk_ashr     := mk_ashr,
  le_mk_ashr  := le_mk_ashr,
  sat_mk_ashr := sat_mk_ashr }

end ashr_default

/-- Typeclass for creating reduction `redand` operators. -/
class redand_factory (β : out_param Type*) (γ : Type*) [factory β γ] :=
(mk_redand      : β → state γ β)
(le_mk_redand   : ∀ {e₁}, increasing (mk_redand e₁))
(sat_mk_redand  : ∀ {g g' : γ} {e₁ e₂ : β} {n : ℕ} {v₁ : fin n → bool},
  (mk_redand e₁).run g = (e₂, g') →
  sat g  e₁ (sigma.mk n v₁) →
  sat g' e₂ (sigma.mk 1 (λ _, bv.all v₁) : (Σ n, fin n → bool)))

namespace redand_default
variables {β γ : Type u} [factory β γ] [eq_factory β γ] [const_factory β γ]
open factory not_factory eq_factory const_factory

/-- Create a `redand` operator. -/
def mk_redand (e : β) : state γ β := do
g ← state_t.get,
let width : ℕ := factory.width g e in do
all_ones : β ← mk_const $ vector.repeat tt width,
mk_eq e all_ones

lemma le_mk_redand ⦃e : β⦄ (g : γ) :
  g ≤ ((mk_redand e).run g).2 :=
begin
  simp only [mk_redand],
  apply increasing_bind,
  { intro r, refl },
  intro c, apply increasing_bind,
  apply le_mk_const,
  intro c, apply le_mk_eq
end

lemma sat_mk_redand ⦃g g' : γ⦄ {e₁ e₂ : β} {n : ℕ} {v₁ : fin n → bool} :
  (mk_redand e₁).run g = (e₂, g') →
  sat g  e₁ (sigma.mk n v₁ : Σ n, fin n → bool) →
  sat g' e₂ ((sigma.mk 1 (λ _, bv.all v₁) : Σ n, fin n → bool)) :=
begin
  intros mk sat₁,
  simp only [mk_redand, state_t.run_bind, state_t.run_get, is_lawful_monad.pure_bind] at mk,
  convert_to _ using 0, swap,
  { apply sat_mk_eq mk; clear mk,
    { exact sat_of_le le_mk_const sat₁ },
    { rw [factory.width_sound sat₁],
      exact sat_mk_const (by rw [prod.mk.eta]) } },
  congr,
  simp only [bv.all],
  ext i,
  rw [← bool.coe_bool_iff],
  rw [list.all_iff_forall, bool.coe_to_bool, function.funext_iff],
  simp only [vector.nth_repeat, list.forall_mem_of_fn_iff, id.def]
end

@[priority 20]
instance : redand_factory β γ :=
{ mk_redand     := mk_redand,
  le_mk_redand  := le_mk_redand,
  sat_mk_redand := sat_mk_redand }

end redand_default

/-- Typeclass for creating reduction `redor` operators. -/
class redor_factory (β : out_param Type*) (γ : Type*) [factory β γ] :=
(mk_redor      : β → state γ β)
(le_mk_redor   : ∀ {e₁}, increasing (mk_redor e₁))
(sat_mk_redor  : ∀ {g g' : γ} {e₁ e₂ : β} {n : ℕ} {v₁ : fin n → bool},
  (mk_redor e₁).run g = (e₂, g') →
  sat g  e₁ (sigma.mk n v₁) →
  sat g' e₂ (sigma.mk 1 (λ _, bv.any v₁) : (Σ n, fin n → bool)))

namespace redor_default
variables {β γ : Type u} [factory β γ] [not_factory β γ] [eq_factory β γ] [const_factory β γ]
open factory not_factory eq_factory const_factory

/-- Create a `redor` operator. -/
def mk_redor (e : β) : state γ β := do
g ← state_t.get,
let width : ℕ := factory.width g e in do
zero : β ← mk_const $ vector.repeat ff width,
eq_zero ← mk_eq e zero,
mk_not eq_zero

lemma le_mk_redor ⦃e : β⦄ (g : γ) :
  g ≤ ((mk_redor e).run g).2 :=
begin
  simp only [mk_redor],
  apply increasing_bind,
  { intro r, refl },
  intro c, apply increasing_bind,
  apply le_mk_const,
  intro c, apply increasing_bind,
  apply le_mk_eq,
  intro c, apply le_mk_not
end

lemma sat_mk_redor ⦃g g' : γ⦄ {e₁ e₂ : β} {n : ℕ} {v₁ : fin n → bool} :
  (mk_redor e₁).run g = (e₂, g') →
  sat g  e₁ (sigma.mk n v₁ : Σ n, fin n → bool) →
  sat g' e₂ ((sigma.mk 1 (λ _, bv.any v₁) : Σ n, fin n → bool)) :=
begin
  intros mk sat₁,
  rw [bv.any_eq_to_bool_nonzero],
  have : (λ (_ : fin 1), to_bool (v₁ ≠ 0)) = bv.not (λ _, to_bool (v₁ = 0)), by simp [bv.not],
  rw [this], clear this,
  simp only [mk_redor, state_t.run_bind, state_t.run_get, is_lawful_monad.pure_bind] at mk,
  apply sat_mk_not mk, clear mk,
  refine sat_mk_eq (by rw [prod.mk.eta]) _ _,
  { exact sat_of_le le_mk_const sat₁ },
  { rw [factory.width_sound sat₁],
    have : (vector.repeat ff n).nth = (0 : fin n → bool),
    { ext i, rw [vector.nth_repeat], refl },
    rw [← this], clear this,
    apply sat_mk_const,
    simp only [prod.mk.eta] }
end

@[priority 20]
instance : redor_factory β γ :=
{ mk_redor     := mk_redor,
  le_mk_redor  := le_mk_redor,
  sat_mk_redor := sat_mk_redor }

end redor_default
end smt
