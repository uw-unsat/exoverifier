/-
Copyright (c) 2021 The UNSAT Group. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luke Nelson, Xi Wang
-/
import data.erased
import data.list.basic
import data.list.forall2
import factory.interface
import misc.bool

universe u

namespace sat
open factory.monad

/-- `factory` specialized to boolean values. -/
abbreviation factory (β γ : Type*) : Type* := factory bool β γ

/-- `factory.decision_procedure` specialized to boolean values. -/
abbreviation decision_procedure (β γ : Type*) [factory β γ] (ω : Type*) : Type* :=
factory.decision_procedure bool β γ ω

/-- `factory.oracle` specialized to boolean values. -/
meta abbreviation oracle (β γ ω : Type) : Type := factory.oracle bool β γ ω

/-- Typeclass for creating constants.

Creating a constant is required not to change the state of the factory.
-/
class const_factory (β : out_param Type*) (γ : Type*) [factory β γ] :=
(mk_const     : γ → bool → β)
(sat_mk_const : ∀ {g : γ} (b : bool), factory.sat g (mk_const g b) b)

namespace const_factory
variables {β γ : Type*} [factory β γ] [const_factory β γ]

/-- Create true. -/
def mk_true : γ → β :=
λ g, mk_const g tt

theorem sat_mk_true : ∀ {g : γ}, factory.sat g (mk_true g : β) tt :=
λ g, sat_mk_const tt

/-- Create false. -/
def mk_false : γ → β :=
λ g, mk_const g ff

theorem sat_mk_false : ∀ {g : γ}, factory.sat g (mk_false g : β) ff :=
λ g, sat_mk_const ff

end const_factory

/-- Typeclass for creating NOT. -/
class not_factory (β : out_param Type*) (γ : Type*) [factory β γ] :=
(mk_not     : ∀ (b : β), state γ β)
(le_mk_not  : ∀ {b : β}, increasing (mk_not b))
(sat_mk_not : ∀ {g g' : γ} {b b' : β} {r : bool},
  (mk_not b).run g = (b', g') →
  factory.sat g b r →
  factory.sat g' b' (!r))

/-- Typeclass for creating variables. -/
class var_factory (β : out_param Type*) (γ : Type*) [factory β γ] :=
(mk_var       : erased bool → state γ β)
(le_mk_var    : ∀ {b : erased bool}, increasing (mk_var b))
(sat_mk_var   : ∀ {g g' : γ} {b : erased bool} {b' : β},
  (mk_var b).run g = (b', g') →
  factory.sat g' b' b.out)

/-- Typeclass for creating AND. -/
class and_factory (β : out_param Type*) (γ : Type*) [factory β γ] :=
(mk_and     : ∀ (b₁ b₂ : β), state γ β)
(le_mk_and  : ∀ {b₁ b₂ : β}, increasing (mk_and b₁ b₂))
(sat_mk_and : ∀ {g g' : γ} {b₁ b₂ b₃ : β} {r₁ r₂ : bool},
  (mk_and b₁ b₂).run g = (b₃, g') →
  factory.sat g b₁ r₁ →
  factory.sat g b₂ r₂ →
  factory.sat g' b₃ (r₁ && r₂))

/-- Typeclass for creating multi-input AND. -/
class all_factory (β : out_param Type*) (γ : Type*) [factory β γ] :=
(mk_all     : ∀ (bs : list β), state γ β)
(le_mk_all  : ∀ {bs : list β}, increasing (mk_all bs))
(sat_mk_all : ∀ {g g' : γ} {bs : list β} {b' : β} {rs : list bool},
  (mk_all bs).run g = (b', g') →
  list.forall₂ (factory.sat g) bs rs →
  factory.sat g' b' (rs.all id))

namespace all_default
variables {β γ : Type u} [factory β γ] [and_factory β γ] [const_factory β γ]
open factory and_factory const_factory

/-- Create a multi-input AND. -/
def mk_all : ∀ (bs : list β), state γ β
| []         := state_t.mk $ λ g, (const_factory.mk_true g, g)
| (hd :: tl) := do
  x ← mk_all tl,
  and_factory.mk_and hd x

lemma le_mk_all : ∀ (bs : list β) (g : γ),
  g ≤ ((mk_all bs).run g).2
| []       _ := by refl
| (hd :: tl) g := by {
  simp only [mk_all, state_t.run_bind],
  simp only [has_bind.bind, id_bind],
  transitivity, swap,
  apply and_factory.le_mk_and,
  apply le_mk_all }

lemma sat_mk_all : ∀ ⦃g g' : γ⦄ {bs : list β} {b' : β} {rs : list bool},
  (mk_all bs).run g = (b', g') →
  list.forall₂ (sat g) bs rs →
  sat g' b' (rs.all id)
| g g' [] _ [] mk' sat := by {
  simp only [list.all_nil],
  cases mk',
  apply const_factory.sat_mk_true }
| g g' (b :: bs) b' (r :: rs) mk' sat := by {
  rw [list.forall₂_cons] at sat,
  cases sat with sat₁ sat₂,
  simp only [mk_all, state_t.run_bind] at mk',
  cases one : (mk_all bs).run g with b₁ g₁,
  specialize sat_mk_all one sat₂,
  simp only [id.def, list.all_cons],
  refine sat_mk_and mk' _ _,
  { exact sat_of_le (le_mk_all _ _) sat₁ },
  { rw [one],
    exact sat_mk_all } }

@[priority 20] -- see Note [lower instance priority]
instance : all_factory β γ :=
{ mk_all     := mk_all,
  le_mk_all  := le_mk_all,
  sat_mk_all := sat_mk_all }

end all_default

/-- Typeclass for creating OR. -/
class or_factory (β : out_param Type*) (γ : Type*) [factory β γ] :=
(mk_or     : ∀ (b₁ b₂ : β), state γ β)
(le_mk_or  : ∀ {b₁ b₂ : β}, increasing (mk_or b₁ b₂))
(sat_mk_or : ∀ {g g' : γ} {b₁ b₂ b₃ : β} {r₁ r₂ : bool},
  (mk_or b₁ b₂).run g = (b₃, g') →
  factory.sat g b₁ r₁ →
  factory.sat g b₂ r₂ →
  factory.sat g' b₃ (r₁ || r₂))

/-- Typeclass for creating multi-input OR. -/
class any_factory (β : out_param Type*) (γ : Type*) [factory β γ] :=
(mk_any     : ∀ (bs : list β), state γ β)
(le_mk_any  : ∀ {bs : list β}, increasing (mk_any bs))
(sat_mk_any : ∀ {g g' : γ} {bs : list β} {b' : β} {rs : list bool},
  (mk_any bs).run g = (b', g') →
  list.forall₂ (factory.sat g) bs rs →
  factory.sat g' b' (rs.any id))

namespace any_default
variables {β γ : Type u} [factory β γ] [or_factory β γ] [const_factory β γ]
open factory or_factory const_factory

/-- Create a multi-input AND. -/
def mk_any : ∀ (bs : list β), state γ β
| []         := state_t.mk $ λ g, (mk_false g, g)
| (hd :: tl) := do
  x ← mk_any tl,
  mk_or hd x

lemma le_mk_any : ∀ (bs : list β) (g : γ),
  g ≤ ((mk_any bs).run g).2
| []       _ := by refl
| (hd :: tl) g := by {
  simp only [mk_any, state_t.run_bind],
  simp only [has_bind.bind, id_bind],
  transitivity, swap,
  apply le_mk_or,
  apply le_mk_any }

lemma sat_mk_any : ∀ ⦃g g' : γ⦄ {bs : list β} {b' : β} {rs : list bool},
  (mk_any bs).run g = (b', g') →
  list.forall₂ (sat g) bs rs →
  sat g' b' (rs.any id)
| g g' [] _ [] mk' sat := by {
  simp only [list.any_nil],
  cases mk',
  apply sat_mk_false }
| g g' (b :: bs) b' (r :: rs) mk' sat := by {
  rw [list.forall₂_cons] at sat,
  cases sat with sat₁ sat₂,
  simp only [mk_any, state_t.run_bind] at mk',
  cases one : (mk_any bs).run g with b₁ g₁,
  specialize sat_mk_any one sat₂,
  simp only [id.def, list.any_cons],
  refine sat_mk_or mk' _ _,
  { exact sat_of_le (le_mk_any _ _) sat₁ },
  { rw [one],
    exact sat_mk_any } }

@[priority 20] -- see Note [lower instance priority]
instance : any_factory β γ :=
{ mk_any     := mk_any,
  le_mk_any  := le_mk_any,
  sat_mk_any := sat_mk_any }

end any_default

/-- Typeclass for creating IMPLIES. -/
class implies_factory (β : out_param Type*) (γ : Type*) [factory β γ] :=
(mk_implies     : ∀ (b₁ b₂ : β), state γ β)
(le_mk_implies  : ∀ {b₁ b₂ : β}, increasing (mk_implies b₁ b₂))
(sat_mk_implies : ∀ {g g' : γ} {b₁ b₂ b₃ : β} {r₁ r₂ : bool},
  (mk_implies b₁ b₂).run g = (b₃, g') →
  factory.sat g b₁ r₁ →
  factory.sat g b₂ r₂ →
  factory.sat g' b₃ (bimplies r₁ r₂))

namespace implies_default
variables {β γ : Type u} [factory β γ] [not_factory β γ] [or_factory β γ]
open factory not_factory or_factory

/-- Create a logical operator `→`. -/
def mk_implies (b₁ b₂ : β) : state γ β := do
t ← mk_not b₁,
mk_or t b₂

lemma le_mk_implies (b₁ b₂ : β) (g : γ) :
  g ≤ ((mk_implies b₁ b₂).run g).2 :=
begin
  simp only [mk_implies, state_t.run_bind],
  transitivity, swap,
  apply le_mk_or,
  apply le_mk_not,
end

lemma sat_mk_implies ⦃g g' : γ⦄ {b₁ b₂ b₃ : β} {r₁ r₂ : bool} :
  (mk_implies b₁ b₂).run g = (b₃, g') →
  sat g b₁ r₁ →
  sat g b₂ r₂ →
  sat g' b₃ (bimplies r₁ r₂) :=
begin
  intros mk sat₁ sat₂,
  simp only [mk_implies, state_t.run_bind] at mk,
  simp only [bimplies_eq_bnot_bor],
  cases step₁ : (mk_not b₁).run g with b₁' g₁,
  refine sat_mk_or mk _ _,
  { rw [step₁],
    exact sat_mk_not step₁ sat₁ },
  { exact sat_of_le le_mk_not sat₂ }
end

@[priority 20] -- see Note [lower instance priority]
instance : implies_factory β γ :=
{ mk_implies     := mk_implies,
  le_mk_implies  := le_mk_implies,
  sat_mk_implies := sat_mk_implies }

end implies_default

/-- Typeclass for creating NIMPLIES. -/
class nimplies_factory (β : out_param Type*) (γ : Type*) [factory β γ] :=
(mk_nimplies     : ∀ (b₁ b₂ : β), state γ β)
(le_mk_nimplies  : ∀ {b₁ b₂ : β}, increasing (mk_nimplies b₁ b₂))
(sat_mk_nimplies : ∀ {g g' : γ} {b₁ b₂ b₃ : β} {r₁ r₂ : bool},
  (mk_nimplies b₁ b₂).run g = (b₃, g') →
  factory.sat g b₁ r₁ →
  factory.sat g b₂ r₂ →
  factory.sat g' b₃ (!bimplies r₁ r₂))

namespace nimplies_default
variables {β γ : Type u} [factory β γ] [not_factory β γ] [and_factory β γ]
open factory not_factory and_factory

/-- Create a logical operator `↛`. -/
def mk_nimplies (b₁ b₂ : β) : state γ β := do
t ← mk_not b₂,
mk_and b₁ t

lemma le_mk_nimplies (b₁ b₂ : β) (g : γ) :
  g ≤ ((mk_nimplies b₁ b₂).run g).2 :=
begin
  simp only [mk_nimplies, state_t.run_bind],
  transitivity, swap,
  apply le_mk_and,
  apply le_mk_not
end

lemma sat_mk_nimplies ⦃g g' : γ⦄ {b₁ b₂ b₃ : β} {r₁ r₂ : bool} :
  (mk_nimplies b₁ b₂).run g = (b₃, g') →
  sat g b₁ r₁ →
  sat g b₂ r₂ →
  sat g' b₃ (!bimplies r₁ r₂) :=
begin
  intros mk sat₁ sat₂,
  simp only [mk_nimplies, state_t.run_bind] at mk,
  rw [bimplies_eq_bnot_bor, bool.bnot_bor, bnot_bnot],
  cases step₁ : (mk_not b₂).run g with b₂' g₁,
  refine sat_mk_and mk _ _,
  { exact sat_of_le le_mk_not sat₁ },
  { rw [step₁],
    exact sat_mk_not step₁ sat₂ }
end

@[priority 20] -- see Note [lower instance priority]
instance : nimplies_factory β γ :=
{ mk_nimplies     := mk_nimplies,
  le_mk_nimplies  := le_mk_nimplies,
  sat_mk_nimplies := sat_mk_nimplies }

end nimplies_default

/-- Typeclass for creating IFF. -/
class iff_factory (β : out_param Type*) (γ : Type*) [factory β γ] :=
(mk_iff       : ∀ (b₁ b₂ : β), state γ β)
(le_mk_iff    : ∀ {b₁ b₂ : β}, increasing (mk_iff b₁ b₂))
(sat_mk_iff : ∀ {g g' : γ} {b₁ b₂ b₃ : β} {r₁ r₂ : bool},
  (mk_iff b₁ b₂).run g = (b₃, g') →
  factory.sat g b₁ r₁ →
  factory.sat g b₂ r₂ →
  factory.sat g' b₃ (biff r₁ r₂))

namespace iff_default
variables {β γ : Type u}  [factory β γ] [and_factory β γ] [implies_factory β γ]
open factory and_factory implies_factory

/-- Create a logical operator `↔`. -/
def mk_iff (b₁ b₂ : β) : state γ β := do
t₁ ← mk_implies b₁ b₂,
t₂ ← mk_implies b₂ b₁,
mk_and t₁ t₂

lemma le_mk_iff (b₁ b₂ : β) (g : γ) :
  g ≤ ((mk_iff b₁ b₂).run g).2 :=
begin
  simp only [mk_iff, state_t.run_bind],
  apply le_trans le_mk_implies,
  apply le_trans le_mk_implies,
  apply le_mk_and
end

lemma sat_mk_iff ⦃g g' : γ⦄ {b₁ b₂ b₃ : β} {r₁ r₂ : bool} :
  (mk_iff b₁ b₂).run g = (b₃, g') →
  sat g b₁ r₁ →
  sat g b₂ r₂ →
  sat g' b₃ (biff r₁ r₂) :=
begin
  intros mk sat₁ sat₂,
  simp only [mk_iff, state_t.run_bind] at mk,
  cases step₁ : (mk_implies b₁ b₂).run g with b₁₂ g₁,
  cases step₂ : (mk_implies b₂ b₁).run g₁ with b₂₁ g₂,
  cases step₃ : (and_factory.mk_and b₁₂ b₂₁).run g₂ with b₁₂₂₁ g₃,
  simp only [biff_eq_bimplies_band_bimplies],
  refine sat.and_factory.sat_mk_and mk _ _,
  { refine sat_of_le le_mk_implies _,
    refine sat_mk_implies _ sat₁ sat₂,
    rw [step₁] },
  { refine sat_mk_implies (by rw [prod.mk.eta]) _ _,
    { exact factory.sat_of_le le_mk_implies sat₂ },
    { exact factory.sat_of_le le_mk_implies sat₁ } }
end

@[priority 20] -- see Note [lower instance priority]
instance : iff_factory β γ :=
{ mk_iff     := mk_iff,
  le_mk_iff  := le_mk_iff,
  sat_mk_iff := sat_mk_iff }

end iff_default

/-- Typeclass for creating XOR. -/
class xor_factory (β : out_param Type*) (γ : Type*) [factory β γ] :=
(mk_xor       : ∀ (b₁ b₂ : β), state γ β)
(le_mk_xor    : ∀ {b₁ b₂ : β}, increasing (mk_xor b₁ b₂))
(sat_mk_xor : ∀ {g g' : γ} {b₁ b₂ b₃ : β} {r₁ r₂ : bool},
  (mk_xor b₁ b₂).run g = (b₃, g') →
  factory.sat g b₁ r₁ →
  factory.sat g b₂ r₂ →
  factory.sat g' b₃ (bxor r₁ r₂))

namespace xor_default
variables {β γ : Type u} [factory β γ] [iff_factory β γ] [not_factory β γ]
open factory iff_factory not_factory

/-- Create a logical operator `XOR`. -/
def mk_xor (b₁ b₂ : β) : state γ β := do
t ← mk_iff b₁ b₂,
mk_not t

lemma le_mk_xor (b₁ b₂ : β) (g : γ) :
  g ≤ ((mk_xor b₁ b₂).run g).2 :=
begin
  simp only [mk_xor, state_t.run_bind],
  transitivity, swap,
  apply le_mk_not,
  apply le_mk_iff,
end

lemma sat_mk_xor ⦃g g' : γ⦄ {b₁ b₂ b₃ : β} {r₁ r₂ : bool} :
  (mk_xor b₁ b₂).run g = (b₃, g') →
  sat g b₁ r₁ →
  sat g b₂ r₂ →
  sat g' b₃ (bxor r₁ r₂) :=
begin
  intros mk sat₁ sat₂,
  simp only [mk_xor, state_t.run_bind] at mk,
  simp only [bxor_eq_bnot_biff],
  refine sat_mk_not mk _,
  exact sat_mk_iff (by rw [prod.mk.eta]) sat₁ sat₂
end

@[priority 20] -- see Note [lower instance priority]
instance : xor_factory β γ :=
{ mk_xor     := mk_xor,
  le_mk_xor  := le_mk_xor,
  sat_mk_xor := sat_mk_xor }

end xor_default

namespace full_add_factory
variables {β γ : Type u} [factory β γ] [and_factory β γ] [or_factory β γ] [xor_factory β γ]
open factory and_factory or_factory xor_factory

/--
Construct a full adder as the following:
* sum  = (x ⊕ y) ⊕ c
* cout = (x && y) || (c && (x ⊕ y))
-/
def mk_full_add (x y c : β) : state γ (β × β) := do
xy ← mk_xor x y,
sum ← mk_xor xy c,
cout ← mjoin $ mk_or <$> mk_and x y <*> mk_and c xy,
pure (sum, cout)

lemma le_mk_full_add {x y c : β} {g : γ} :
  g ≤ ((mk_full_add x y c).run g).2 :=
begin
  simp only [mk_full_add, mjoin],
  simp only [← bind_pure_comp_eq_map, ← bind_map_eq_seq],
  simp only [state_t.run_bind, state_t.run_pure],
  apply le_trans _ le_mk_or,
  apply le_trans _ le_mk_and,
  apply le_trans _ le_mk_and,
  apply le_trans _ le_mk_xor,
  apply le_mk_xor
end

theorem sat_mk_full_add ⦃g g' : γ⦄ {x y c sum cout : β} {x_b y_b c_b : bool} :
  (mk_full_add x y c).run g = ((sum, cout), g') →
  sat g x x_b →
  sat g y y_b →
  sat g c c_b →
    sat g' sum (bxor (bxor x_b y_b) c_b) ∧
    sat g' cout ((x_b && y_b) || (c_b && (bxor x_b y_b))) :=
begin
  intros mk sat_x sat_y sat_c,
  simp only [mk_full_add, mjoin] at mk,
  simp only [← bind_pure_comp_eq_map, ← bind_map_eq_seq] at mk,
  simp only [state_t.run_bind, state_t.run_pure] at mk,
  simp only [pure, id, has_bind.bind, id_bind] at mk,
  rw [prod.eq_iff_fst_eq_snd_eq] at mk,
  cases mk with mk₁ mk₂,
  split,
  { cases mk₁, cases mk₂, clear mk₁ mk₂,
    refine sat_of_le (le_trans le_mk_and (le_trans le_mk_and le_mk_or)) _,
    refine sat_mk_xor (by rw [prod.mk.eta]) _ _,
    { exact sat_mk_xor (by rw [prod.mk.eta]) sat_x sat_y },
    { exact sat_of_le (by apply le_mk_xor) sat_c } },
  { cases mk₁, cases mk₂, clear mk₁ mk₂,
    refine sat_mk_or (by rw [prod.mk.eta]) _ _,
    { refine sat_of_le le_mk_and _,
      refine sat_mk_and (by rw [prod.mk.eta]) _ _,
      { exact sat_of_le (le_trans le_mk_xor le_mk_xor) sat_x },
      { exact sat_of_le (le_trans le_mk_xor le_mk_xor) sat_y } },
    { refine sat_mk_and (by rw [prod.mk.eta]) _ _,
      { exact sat_of_le (le_trans le_mk_xor (le_trans le_mk_xor le_mk_and)) sat_c },
      { refine sat_of_le (le_trans le_mk_xor le_mk_and) _,
        exact sat_mk_xor (by rw [prod.mk.eta]) sat_x sat_y } } }
end

lemma sat_mk_full_add_sum ⦃g g' : γ⦄ {x y c sum cout : β} {x_b y_b c_b : bool} :
  (mk_full_add x y c).run g = ((sum, cout), g') →
  sat g x x_b →
  sat g y y_b →
  sat g c c_b →
  sat g' sum (bxor (bxor x_b y_b) c_b) :=
begin
  intros mk sat_x sat_y sat_c,
  obtain ⟨h, _⟩ := sat_mk_full_add mk sat_x sat_y sat_c,
  from h
end

lemma sat_mk_full_add_carry ⦃g g' : γ⦄ {x y c sum cout : β} {x_b y_b c_b : bool} :
  (mk_full_add x y c).run g = ((sum, cout), g') →
  sat g x x_b →
  sat g y y_b →
  sat g c c_b →
  sat g' cout ((x_b && y_b) || (c_b && (bxor x_b y_b))) :=
begin
  intros mk sat_x sat_y sat_c,
  obtain ⟨_, h⟩ := sat_mk_full_add mk sat_x sat_y sat_c,
  from h
end

end full_add_factory

namespace ult_factory
variables {β γ : Type u} [factory β γ] [and_factory β γ] [or_factory β γ] [implies_factory β γ]
                         [nimplies_factory β γ]
open factory and_factory or_factory implies_factory nimplies_factory

/-- Construct an unsigned less-than comparator as the following:
* input: `x`, `y`, and carry `c`
* output: `((!x || y) && c) || (!x && y)`
-/
def mk_ult (x y c : β) : state γ β := do
xy ← mk_implies x y,
t ← mk_and c xy,
yx ← mk_nimplies y x,
mk_or t yx

lemma le_mk_ult {x y c : β} {g : γ} :
  g ≤ ((mk_ult x y c).run g).2 :=
begin
  simp only [mk_ult],
  simp only [state_t.run_bind, state_t.run_pure],
  apply le_trans _ le_mk_or,
  apply le_trans _ le_mk_nimplies,
  apply le_trans le_mk_implies le_mk_and
end

lemma sat_mk_ult ⦃g g' : γ⦄ {x y c r : β} {x_b y_b c_b : bool} :
  (mk_ult x y c).run g = (r, g') →
  sat g x x_b →
  sat g y y_b →
  sat g c c_b →
  sat g' r ((c_b && bimplies x_b y_b) || !bimplies y_b x_b) :=
begin
  intros mk sat_x sat_y sat_c,
  simp only [mk_ult] at mk,
  simp only [state_t.run_bind, state_t.run_pure] at mk,
  simp only [pure, id, has_bind.bind, id_bind] at mk,
  simp only [prod.eq_iff_fst_eq_snd_eq] at mk,
  cases mk with mk₁ mk₂,
  cases mk₁, cases mk₂, clear mk₁ mk₂,
  refine sat_mk_or (by rw [prod.mk.eta]) _ _,
  { refine sat_of_le le_mk_nimplies _,
    refine sat_mk_and (by rw [prod.mk.eta]) _ _,
    { exact sat_of_le le_mk_implies sat_c },
    { exact sat_mk_implies (by rw [prod.mk.eta]) sat_x sat_y } },
  { refine sat_mk_nimplies (by rw [prod.mk.eta]) _ _;
    apply sat_of_le (le_trans le_mk_implies le_mk_and);
    assumption }
end

end ult_factory

/-- Typeclass for creating AND. -/
class ite_factory (β : out_param Type*) (γ : Type*) [factory β γ] :=
(mk_ite     : ∀ (b₁ b₂ b₃ : β), state γ β)
(le_mk_ite  : ∀ {b₁ b₂ b₃ : β}, increasing (mk_ite b₁ b₂ b₃))
(sat_mk_ite : ∀ {g g' : γ} {b₁ b₂ b₃ b₄ : β} {r₁ r₂ r₃ : bool},
  (mk_ite b₁ b₂ b₃).run g = (b₄, g') →
  factory.sat g b₁ r₁ →
  factory.sat g b₂ r₂ →
  factory.sat g b₃ r₃ →
  factory.sat g' b₄ (cond r₁ r₂ r₃))

namespace default_ite
variables {β γ : Type u} [factory β γ] [or_factory β γ] [and_factory β γ] [not_factory β γ]
open factory or_factory and_factory not_factory

private lemma ite_eq_or_and_conds (c x y : bool) :
  (cond c x y) = ((c && x) || (!c && y)) :=
by cases c; simp

/-- Construct an if-then-else circuit. -/
def mk_ite (c x y : β) : state γ β := do
cx ← mk_and c x,
nc ← mk_not c,
ncy ← mk_and nc y,
mk_or cx ncy

lemma le_mk_ite : ∀ (c x y : β) (g : γ),
  g ≤ ((mk_ite c x y).run g).2 :=
begin
  intros _ _ _ _,
  simp only [mk_ite],
  apply increasing_bind; intros,
  apply le_mk_and,
  apply increasing_bind; intros,
  apply le_mk_not,
  apply increasing_bind; intros,
  apply le_mk_and,
  apply le_mk_or
end

theorem sat_mk_ite ⦃g g' : γ⦄ {c x y out : β} {c_b x_b y_b: bool} :
  (mk_ite c x y).run g = (out, g') →
  sat g  c   c_b →
  sat g  x   x_b →
  sat g  y   y_b →
  sat g' out (cond c_b x_b y_b) :=
begin
  intros mk sat₁ sat₂ sat₃,
  simp only [mk_ite, state_t.run_bind] at mk,
  rw [ite_eq_or_and_conds],
  refine sat_mk_or mk _ _,
  { refine sat_of_le (le_trans le_mk_not le_mk_and) _,
    exact sat_mk_and (by rw [prod.mk.eta]) sat₁ sat₂ },
  { refine sat_mk_and (by rw [prod.mk.eta]) _ _,
    { refine sat_mk_not (by rw [prod.mk.eta]) _,
      exact sat_of_le le_mk_and sat₁ },
    { exact sat_of_le (le_trans le_mk_and le_mk_not) sat₃ } }
end

@[priority 20]
instance : ite_factory β γ :=
{ mk_ite     := mk_ite,
  le_mk_ite  := le_mk_ite,
  sat_mk_ite := sat_mk_ite }

end default_ite
end sat
