/-
Copyright (c) 2021 The UNSAT Group. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luke Nelson, Xi Wang
-/
import misc.with_bot
import misc.with_top
import order.bounded_lattice
import data.fintype.basic

/-!
# Abstract domains

Basic definitions of domains for abstract interpretation.

## References

* <https://xavierleroy.org/courses/Eugene-2011/Analyzer1.html>
* <https://xavierleroy.org/courses/Eugene-2011/Analyzer2.html>
* <https://hal.archives-ouvertes.fr/tel-01327023/document>
-/

/--
has_γ β α means that the type α can serve as an abstraction of sets of concrete values of type β.
There are two definitions that must be met:
A function γ which maps an abstract value to its set of concrete values; and
a function `abstract` which maps a single concrete value into an abstract value.

Assume that α uniquely determines β.
-/
class has_γ (β : out_param Type*) (α : Type*) :=
(γ                : α → set β)
(abstract         : β → α)
(abstract_correct : ∀ (x : β), x ∈ γ (abstract x))

open has_γ

/--
has_decidable_γ is has_γ when the γ relation is decidable.
-/
class has_decidable_γ (β : out_param Type*) (α : Type*) extends has_γ β α :=
(dec_γ : ∀ (x : α), decidable_pred (γ x))

/--
abstr_le β α is an ordering on abstract values that respects set inclusion using γ.
-/
class abstr_le (β : out_param Type*) (α : Type*) [has_γ β α] extends has_le α :=
(dec_le     : decidable_rel le)
(le_correct : ∀ ⦃x y : α⦄, x ≤ y → γ x ⊆ γ y)

/--
abstr_top β α means there exists an element ⊤ that maps to the complete set of β.
-/
class abstr_top (β : out_param Type*) (α : Type*) [has_γ β α] extends has_top α :=
(top_correct : ∀ (c : β), γ top c)

/--
abstr_bot β α means there exists an element ⊥ that maps to the empty set of β.
-/
class abstr_bot (β : out_param Type*) (α : Type*) [has_γ β α] extends has_bot α :=
(bot_correct : ∀ (c : β), ¬(γ bot c))

/--
abstr_join β α means that there exists a join operation which respects set union using γ.
-/
class abstr_join (β : out_param Type*) (α₁ α₂ : Type*) [has_γ β α₁] [has_γ β α₂] :=
(join         : α₁ → α₁ → α₂)
(join_correct : ∀ ⦃x y : α₁⦄, γ x ∪ γ y ⊆ γ (join x y))

/--
abstr_meet β α means that there exists a meet operation which respects set intersection using γ.
-/
class abstr_meet (β : out_param Type*) (α₁ α₂ : Type*) [has_γ β α₁] [has_γ β α₂] :=
(meet         : α₁ → α₁ → α₂)
(meet_correct : ∀ ⦃x y : α₁⦄, γ x ∩ γ y ⊆ γ (meet x y))

/--
A test function for abstract values. Given some test `p` on concrete values,
it determines whether that test is satisfied for all concrete values represented by the
abstract value.
-/
structure abstr_unary_test (β α : Type*) [has_γ β α] (p : β → bool) :=
(test       : α → bool)
(test_sound : ∀ ⦃x : β⦄ ⦃u : α⦄,
  test u = tt →
  x ∈ γ u →
  p x = tt)

structure abstr_binary_test (β α : Type*) [has_γ β α] (p : β → β → bool) :=
(test       : α → α → bool)
(test_sound : ∀ ⦃x y : β⦄ ⦃u v : α⦄,
  test u v = tt →
  x ∈ γ u →
  y ∈ γ v →
  p x y = tt)

structure abstr_unary_transfer (β α₁ α₂ : Type*) [has_γ β α₁] [has_γ β α₂] (f : β → β) :=
(op      : α₁ → α₂)
(correct : ∀ ⦃x : β⦄ ⦃u : α₁⦄,
  x ∈ γ u →
  (f x) ∈ γ (op u))

structure abstr_binary_transfer (β₁ β₂ α₁ α₂ : Type*) [has_γ β₁ α₁] [has_γ β₂ α₂] (f : β₁ → β₁ → β₂) :=
(op      : α₁ → α₁ → α₂)
(correct : ∀ ⦃x y : β₁⦄ ⦃u v : α₁⦄,
  x ∈ γ u →
  y ∈ γ v →
  (f x y) ∈ γ (op u v))

structure abstr_unary_inversion (β α₁ α₂ : Type*) [has_γ β α₁] [has_γ β α₂] (p : β → Prop) :=
(inv     : α₁ → α₂)
(correct : ∀ ⦃x : β⦄ ⦃u : α₁⦄,
  x ∈ γ u →
  p x →
  x ∈ γ (inv u))

structure abstr_binary_inversion (β α₁ α₂ : Type*) [has_γ β α₁] [has_γ β α₂] (p : β → β → Prop) :=
(inv     : α₁ → α₁ → (α₂ × α₂))
(correct : ∀ ⦃x y : β⦄ ⦃u v : α₁⦄,
  x ∈ γ u →
  y ∈ γ v →
  p x y →
    x ∈ γ (inv u v).1 ∧ y ∈ γ (inv u v).2)

section

variables {β α : Type*}

instance [has_decidable_γ β α] (x : α) : decidable_pred (γ x) := has_decidable_γ.dec_γ _

instance [has_decidable_γ β α] (x : α) (y : β) : decidable (y ∈ γ x) := has_decidable_γ.dec_γ _ _

namespace abstr_join
instance to_has_sup [has_γ β α] [abstr_join β α α] : has_sup α := ⟨abstr_join.join⟩
end abstr_join

namespace abstr_meet
instance to_has_inf [has_γ β α] [abstr_meet β α α] : has_inf α := ⟨abstr_meet.meet⟩
end abstr_meet

instance [has_γ β α] [abstr_le β α] : decidable_rel (@has_le.le α _) :=
  abstr_le.dec_le

namespace id

/-
Lattice operations on id α defined using equality.
-/

instance : has_γ α (id α) :=
{ γ                := eq,
  abstract         := id,
  abstract_correct := by tauto }

instance [decidable_eq α] : has_decidable_γ α (id α) :=
{ dec_γ := infer_instance }

instance [decidable_eq α] : abstr_le α (id α) :=
{ le         := eq,
  dec_le     := infer_instance,
  le_correct := by { rintros _ _ ⟨⟩, refl } }

def transfer (f : α → α → α) : abstr_binary_transfer α α (id α) (id α) f :=
{ op      := f,
  correct := by { rintros _ _ _ _ ⟨⟩ ⟨⟩, constructor } }

end id

namespace fn

/-
Lifting lattice operations on α to functions of type κ → α.
When κ is finite, ≤ and γ are decidable if the corresponding operations on the lattice α are too.
-/

variables {κ α' : Type*}
open abstr_top abstr_join abstr_meet

instance [has_γ β α] : has_γ (κ → β) (κ → α) :=
{ γ                := λ g f, ∀ i, f i ∈ γ (g i),
  abstract         := λ f, abstract ∘ f,
  abstract_correct := by {
    intros _ _,
    apply abstract_correct } }

instance [fintype κ] [has_γ β α] [abstr_le β α] : abstr_le (κ → β) (κ → α) :=
{ le         := λ a b, ∀ i, a i ≤ b i,
  le_correct := λ _ _ h₁ _ h₂ _, abstr_le.le_correct (h₁ _) (h₂ _),
  dec_le     := λ _ _, fintype.decidable_forall_fintype }

instance [fintype κ] [has_decidable_γ β α] : has_decidable_γ (κ → β) (κ → α) :=
{ dec_γ := λ _ _, by {
    apply' fintype.decidable_forall_fintype } }

instance [has_γ β α] [abstr_top β α] : abstr_top (κ → β) (κ → α) :=
{ top_correct := λ _ _, by apply top_correct }

instance [has_γ β α] [has_γ β α'] [abstr_join β α α'] : abstr_join (κ → β) (κ → α) (κ → α') :=
{ join         := λ f₁ f₂ i, join (f₁ i) (f₂ i),
  join_correct := by {
    intros _ _ _ h _,
    apply join_correct,
    cases h,
    { left, tauto },
    { right, tauto } } }

instance [has_γ β α] [has_γ β α'] [abstr_meet β α α'] : abstr_meet (κ → β) (κ → α) (κ → α') :=
{ meet         := λ f₁ f₂ i, meet (f₁ i) (f₂ i),
  meet_correct := by {
    intros _ _ _ h _,
    apply meet_correct,
    cases h,
    split; tauto } }

end fn

namespace prod

/-
Lifting lattice operations on α₁ and α₂ to (α₁ × α₂).
-/

variables {α₁ α₂ δ₁ δ₂ : Type}
open abstr_le abstr_join abstr_top

instance [has_γ β α₁] [has_γ β α₂] : has_γ β (α₁ × α₂) :=
{ γ                := λ (a : α₁ × α₂) (x : β), γ a.fst x ∧ γ a.snd x,
  abstract         := λ x, (abstract x, abstract x),
  abstract_correct := by {
    intros _,
    split; apply abstract_correct } }

instance [has_decidable_γ β α₁] [has_decidable_γ β α₂] : has_decidable_γ β (α₁ × α₂) :=
{ dec_γ := infer_instance }

instance [has_γ β δ₁] [has_γ β δ₂] [has_γ β α₁] [has_γ β α₂] [abstr_join β δ₁ α₁] [abstr_join β δ₂ α₂] :
  abstr_join β (δ₁ × δ₂) (α₁ × α₂) :=
{ join         := λ ⟨d₁, d₂⟩ ⟨d₃, d₄⟩, ⟨join d₁ d₃, join d₂ d₄⟩,
  join_correct := by {
    intros x y,
    cases x, cases y,
    simp only [γ, abstr_join._match_2, abstr_join._match_1],
    rintros a h,
    simp only [set.mem_union_eq] at h,
    split; apply join_correct;
      cases h; cases h with h1 h2;
      try{ left; { exact h1 <|> exact h2 } };
      try{ right; { exact h1 <|> exact h2 } } } }

instance [has_γ β α₁] [has_γ β α₂] [abstr_le β α₁] [abstr_le β α₂] :
  abstr_le β (α₁ × α₂) :=
{ dec_le     := infer_instance,
  le_correct := by {
    rintros _ _ ⟨h₁l, h₁r⟩ x ⟨h₂l, h₂r⟩,
    split,
    { exact le_correct h₁l h₂l },
    { exact le_correct h₁r h₂r } } }

instance [has_γ β α₁] [has_γ β α₂] [abstr_top β α₁] [abstr_top β α₂] :
  abstr_top β (α₁ × α₂) :=
{ top_correct := by {
    intros _,
    split; apply top_correct } }

end prod

namespace with_bot

/-
Lifting lattice operations on α to α+⊥, additionally granting `abstr_bot`.
-/

open abstr_le abstr_join abstr_top abstr_bot

instance [has_γ β α] : has_γ β (with_bot α) :=
{ γ :=
  λ (x : with_bot α),
    match x with
    | some y := γ y
    | none   := ∅
    end,
  abstract         := λ x, some (abstract x),
  abstract_correct := by {
    intros _,
    apply abstract_correct } }

instance [has_decidable_γ β α] : has_decidable_γ β (with_bot α) :=
{ dec_γ := λ (a : with_bot α) (x : β),
    match a with
    | none    := is_false false.elim
    | some a' := dite (γ a' x) is_true is_false
    end }

instance [has_γ β α] : abstr_bot β (with_bot α) :=
{ bot_correct := by rintros _ ⟨⟩ }

instance [has_γ β α] [abstr_top β α] : abstr_top β (with_bot α) :=
{ top         := some ⊤,
  top_correct := by {
    intros, dsimp only [γ, with_bot.has_γ._match_1],
    apply top_correct } }

instance [has_γ β α] [abstr_le β α] : abstr_le β (with_bot α) :=
{ le := λ (x y : with_bot α),
    match x, y with
    | some x, some y := x ≤ y
    | ⊥,      _      := true
    | _,      ⊥      := false
    end,
  dec_le := λ (a b : with_bot α),
    match a, b with
    | some x, some y := dite (x ≤ y) is_true is_false
    | none,   some _ := is_true true.intro
    | some _, none   := is_false false.elim
    | none,   none   := is_true true.intro
    end,
  le_correct := by {
    intros x y h, cases x; cases y,
    { cases h,
      intros _, exact id },
    { rintros _ ⟨⟩ },
    { cases h },
    { dsimp only [γ, with_bot.has_γ._match_1],
      exact le_correct h } } }

instance join_args [has_γ β α] [abstr_join β α (with_bot α)] :
  abstr_join β (with_bot α) (with_bot α) :=
{ join := λ (x y : with_bot α),
    match x, y with
    | some x, some y := join x y
    | some z, none   := some z
    | none,   some z := some z
    | _,      _      := ⊥
    end,
  join_correct := by {
    intros x y z h,
    cases x; cases y; simp only [join_args._match_1]; cases h; try{cases h};
      dsimp only [γ, has_γ._match_1] at h,
    { dsimp only [γ, has_γ._match_1]; assumption },
    { dsimp only [γ, has_γ._match_1]; assumption },
    { apply join_correct; left; assumption },
    { apply join_correct; right; assumption } } }

instance join_res [has_γ β α] [abstr_join β α α] :
  abstr_join β α (with_bot α) :=
{ join         := λ (x y : α), some $ abstr_join.join x y,
  join_correct := by {
    intros x y z h,
    dsimp only [γ, has_γ._match_1],
    apply abstr_join.join_correct,
    exact h } }

instance meet_args [has_γ β α] [abstr_meet β α (with_bot α)] :
  abstr_meet β (with_bot α) (with_bot α) :=
{ meet := λ (x y : with_bot α),
    match x, y with
    | some x, some y := abstr_meet.meet x y
    | _,      _      := ⊥
    end,
  meet_correct := by {
    intros x y z h,
    cases h with zx zy,
    cases x; cases y; dsimp only [meet_args._match_1];
      try{cases zx}; try{cases zy},
    apply abstr_meet.meet_correct,
    dsimp only [γ, has_γ._match_1] at *,
    split; assumption } }

def lift_unary_test {p : β → bool} [has_γ β α] (g : abstr_unary_test β α p) :
  abstr_unary_test β (with_bot α) p :=
{ test := λ (x : with_bot α),
    match x with
    | ⊥        := tt -- If ⊥, then the test is trivially satisfied for all elements.
    | (some x) := g.test x
    end,
  test_sound := by {
    intros _ _ test_tt xu,
    cases u,
    { cases xu },
    { apply g.test_sound test_tt xu } } }

def lift_arg_unary_inversion {p : β → Prop} [has_γ β α] (g : abstr_unary_inversion β α (with_bot α) p) :
  abstr_unary_inversion β (with_bot α) (with_bot α) p :=
{ inv     := λ (x : with_bot α), x >>= g.inv,
  correct := by {
    intros _ _ xu h,
    cases u,
    { exact xu },
    { simp only [option.some_bind],
      exact g.correct xu h } } }

/-- Lift a unary transfer function to work with ⊥. -/
def lift_unary_transfer {f : β → β} [has_γ β α] (g : abstr_unary_transfer β α α f) :
  abstr_unary_transfer β (with_bot α) (with_bot α) f :=
{ op := λ (x : with_bot α), g.op <$> x,
  correct := by {
    intros x u xu,
    cases u,
    { cases xu },
    { exact g.correct xu } } }

/-- Lift a binary transfer function to work with ⊥. -/
def lift_binary_transfer {f : β → β → β} [has_γ β α] (g : abstr_binary_transfer β β α α f) :
  abstr_binary_transfer β β (with_bot α) (with_bot α) f :=
{ op := λ (x y : with_bot α), g.op <$> x <*> y,
  correct := by {
    intros x y u v xu yv,
    cases u; cases v; simp [has_seq.seq],
    { cases xu },
    { cases xu },
    { cases yv },
    { apply g.correct,
      exact xu,
      exact yv } } }

end with_bot

namespace with_top

/-
Lifting lattice operations on α to α+⊤, additionally granting `abstr_top`.
-/

open abstr_bot abstr_join

instance [has_γ β α] : has_γ β (with_top α) :=
{ γ := λ (x : with_top α),
    match x with
    | some y := γ y
    | none   := ⊤
    end,
  abstract         := λ x, some (abstract x),
  abstract_correct := by {
    intros _,
    apply abstract_correct } }

instance [has_decidable_γ β α] : has_decidable_γ β (with_top α) :=
{ dec_γ := λ (a : with_top α) (x : β),
    match a with
    | none    := is_true true.intro
    | some a' := dite (γ a' x) is_true is_false
    end }

instance [has_γ β α] : abstr_top β (with_top α) :=
{ top_correct := by { intros, triv } }

instance [has_γ β α] [abstr_bot β α] : abstr_bot β (with_top α) :=
{ bot         := some ⊥,
  bot_correct := by {
    intros,
    apply bot_correct } }

instance [has_γ β α] [abstr_le β α] : abstr_le β (with_top α) :=
{ le :=
  λ (x y : with_top α),
    match x, y with
    | some x, some y := x ≤ y
    | _,      ⊤      := true
    | ⊤,      _      := false
    end,
  dec_le := λ (a b : with_top α),
    match a, b with
    | some x, some y := dite (x ≤ y) is_true is_false
    | none,   some _ := is_false false.elim
    | some _, none   := is_true true.intro
    | none,   none   := is_true true.intro
    end,
  le_correct := by {
    intros x y h, cases x; cases y,
    { cases h,
      intros _, exact id },
    { intros x h, cases h, cases h },
    { dsimp only [γ, with_top.has_γ._match_1],
      intros _ _, exact true.intro },
    { apply abstr_le.le_correct h } } }

-- A default instance of join.
instance [decidable_eq α] : abstr_join α (id α) (with_top (id α)) :=
{ join := λ x y, if x = y then some x else ⊤,
  join_correct := by {
    intros x y z h,
    split_ifs with h',
    { subst_vars,
      cases h; exact h },
    { apply abstr_top.top_correct } } }

instance join_args [has_γ β α] [abstr_join β α (with_top α)] :
  abstr_join β (with_top α) (with_top α) :=
{ join := λ (x y : with_top α),
    match x, y with
    | some x, some y := join x y
    | _,      _      := ⊤
    end,
  join_correct := by {
    intros x y z h,
    cases x; cases y; simp only [join_args._match_1],
    apply join_correct,
    exact h } }

/--
Lift a binary function that can return ⊤ to accept ⊤ as an argument.
Note this is not always the most precise approximation for `f`, for example,
if `f` is MOV (i.e., λ _ y, y), then this is less precise than simply returning the
right operand.
-/
def lift_binary_transfer_arg {f : β → β → β} [has_γ β α] (g : abstr_binary_transfer β β α (with_top α) f) :
  abstr_binary_transfer β β (with_top α) (with_top α) f :=
{ op := (λ (x y : with_top α), do
    x' ← x,
    y' ← y,
    g.op x' y'),
  correct := by {
    intros x y u v xu yv,
    cases u; cases v; simp only [option.some_bind],
    apply g.correct xu yv } }

/--
Lift a transfer function to `with_top`. Note that, like `lift_binary_transfer_arg`,
this is not always maximally precise.
-/
def lift_binary_transfer {f : β → β → β} [has_γ β α] (g : abstr_binary_transfer β β α α f) :
  abstr_binary_transfer β β (with_top α) (with_top α) f :=
lift_binary_transfer_arg {
  op := λ x y, some $ g.op x y,
  correct := by {
    intros _ _ _ _ _ _,
    apply g.correct; assumption } }

end with_top
end

namespace abstr_meet
open abstr_meet
variables {α β : Type*} [has_γ β α] [abstr_meet β α (with_bot α)]

def invert_equality : abstr_binary_inversion β α (with_bot α) eq :=
{ inv := λ (x y : α), let z : with_bot α := meet x y in (z, z),
  correct := by {
    intros x y u v xu yv x_eq_y,
    subst x_eq_y,
    simp only [and_self],
    apply meet_correct ⟨xu, yv⟩ } }

end abstr_meet

namespace abstr_binary_inversion
open abstr_join abstr_meet
variables {α α' β : Type*} [has_γ β α] [has_γ β α']

/-- A trivial inversion that learns nothing. -/
def trivial {f} : abstr_binary_inversion β α (with_bot α) f :=
{ inv := λ x y, (some x, some y),
  correct := by {
    intros _ _ _ _ h₁ h₂ _,
    exact ⟨h₁, h₂⟩ } }

def invert_disjunction {f g} [abstr_join β α' α']
    (inv₁ : abstr_binary_inversion β α α' f)
    (inv₂ : abstr_binary_inversion β α α' g) :
  abstr_binary_inversion β α α' (λ x y, f x y ∨ g x y) :=
{ inv := λ (x y : α), (inv₁.inv x y) ⊔ (inv₂.inv x y),
  correct := by {
    rintros _ _ _ _ xu yv (h₁ | h₁),
    { obtain ⟨hl, hr⟩ := inv₁.correct xu yv h₁,
      exact ⟨join_correct (or.inl hl), join_correct (or.inl hr)⟩ },
    { obtain ⟨hl, hr⟩ := inv₂.correct xu yv h₁,
      exact ⟨join_correct (or.inr hl), join_correct (or.inr hr)⟩ } } }

def invert_conjunction {f g} [abstr_meet β α' α']
    (inv₁ : abstr_binary_inversion β α α' f)
    (inv₂ : abstr_binary_inversion β α α' g) :
  abstr_binary_inversion β α α' (λ x y, f x y ∧ g x y) :=
{ inv := λ (x y : α), (inv₁.inv x y) ⊓ (inv₂.inv x y),
  correct := by {
    rintros _ _ _ _ xu yv ⟨h₁, h₂⟩,
    obtain ⟨hl₁, hr₁⟩ := inv₁.correct xu yv h₁,
    obtain ⟨hl₂, hr₂⟩ := inv₂.correct xu yv h₂,
    exact ⟨meet_correct ⟨hl₁, hl₂⟩, meet_correct ⟨hr₁, hr₂⟩⟩ } }

def invert_swap {f}
    (inv : abstr_binary_inversion β α α' f) :
  abstr_binary_inversion β α α' (function.swap f) :=
{ inv := λ (x y : α), (inv.inv y x).swap,
  correct := by {
    intros _ _ _ _ xu yv h₁,
    have h₂ := inv.correct yv xu h₁,
    rw [and_comm],
    exact h₂ } }

end abstr_binary_inversion

-- Kill dangerous_instance lint warnings all at once.
attribute [nolint dangerous_instance]
  abstr_le.to_has_le abstr_top.to_has_top abstr_bot.to_has_bot
  abstr_join.to_has_sup abstr_meet.to_has_inf

-- Set priorities from warnings
attribute [priority 100]
  abstr_join.to_has_sup abstr_meet.to_has_inf
