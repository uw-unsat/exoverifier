/-
Copyright (c) 2021 The UNSAT Group. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luke Nelson, Xi Wang
-/
import .basic
import .bv
import data.bv.basic
import data.bv.circuit
import misc.bool
import misc.vector

/-!
# Tristate numbers (tnum)

Each bit in a tnum can be either 0, 1, or unknown.
-/

/-- A tnum is represented by a value and a mask. -/
@[derive decidable_eq]
structure tnum (n : ℕ) : Type :=
(value mask : lsbvector n)

namespace tnum
variable {n : ℕ}

private meta def to_pexpr' (t : tnum n) : pexpr :=
``(tnum.mk %%t.value %%t.mask)

meta instance : has_to_pexpr (tnum n) := ⟨to_pexpr'⟩

def cons (value mask : bool) (x : tnum n) : tnum (n + 1) :=
⟨ value ::ᵥ x.value,
  mask ::ᵥ x.mask ⟩

def tail (x : tnum n) : tnum (n - 1) :=
⟨ vector.tail x.value,
  vector.tail x.mask ⟩

instance : has_repr (tnum n) :=
⟨ λ t, "⟨" ++ repr t.value ++ ", " ++ repr t.mask ++ "⟩" ⟩

instance : subsingleton (tnum 0) :=
⟨λ x y, by { cases x, cases y, cc }⟩

protected def rel (value mask actual : bool) : bool :=
cond mask (!value) (biff value actual)

/-- Concretization function. -/
def γ (f : tnum n) : set (fin n → bool) :=
λ f', ∀ i, tnum.rel (f.value.nth i) (f.mask.nth i) (f' i) = tt

@[reducible]
protected def is_const (x : tnum n) : Prop :=
x.mask = vector.repeat ff n

private theorem γ_is_const {x : tnum n} {a : fin n → bool} :
  a ∈ γ x →
  x.is_const →
  x.value = vector.of_fn a :=
begin
  intros h₁ h₂,
  ext i,
  specialize h₁ i,
  simp only [tnum.is_const] at h₂,
  simp only [h₂, vector.nth_repeat, tnum.rel, cond, biff_eq_tt_iff_eq] at h₁,
  simp only [h₁, vector.nth_of_fn]
end

private theorem γ_cons_iff {x : tnum n} {value mask : bool} {a : fin n.succ → bool} :
  a ∈ γ (tnum.cons value mask x) ↔
  (tnum.rel value mask (a 0) = tt ∧ fin.tail a ∈ γ x) :=
begin
  simp only [tnum.cons],
  split,
  { intros h,
    split,
    { specialize h 0,
      simp only [vector.nth_cons_zero] at h,
      exact h },
    { intros i,
      specialize h i.succ,
      simp only [vector.nth_cons_succ] at h,
      exact h } },
  { intros h i,
    refine fin.cases _ _ i,
    { simp only [vector.nth_zero, vector.head_cons],
      exact h.1 },
    { rcases h with ⟨-, h⟩,
      intros j,
      specialize h j,
      simp only [tnum.tail, vector.nth_tail, vector.nth_cons_succ] at h ⊢,
      exact h } }
end

private theorem γ_iff_head_tail {x : tnum n.succ} {a : fin n.succ → bool} :
  a ∈ γ x ↔
  (tnum.rel x.value.head x.mask.head (a 0) = tt ∧ fin.tail a ∈ γ x.tail) :=
begin
  split,
  { intros h,
    split,
    { specialize h 0,
      simp only [vector.nth_zero] at h,
      exact h },
    { intros i,
      specialize h i.succ,
      simp only [tnum.tail, vector.nth_tail_succ] at h ⊢,
      exact h } },
  { intros h i,
    refine fin.cases _ _ i,
    { simp only [vector.nth_zero],
      exact h.1 },
    { rcases h with ⟨-, h⟩,
      intros j,
      specialize h j,
      simp only [tnum.tail, vector.nth_tail_succ] at h ⊢,
      exact h } }
end

/-- Create a tnum for a constant. -/
protected def const (f : fin n → bool) : tnum n :=
⟨ vector.of_fn f, vector.repeat ff _ ⟩

protected theorem const_correct {f : fin n → bool} :
  f ∈ γ (tnum.const f) :=
begin
  simp only [tnum.const, γ],
  intros i,
  simp only [vector.nth_of_fn, vector.nth_repeat],
  cases (f i); refl
end

instance : has_decidable_γ (fin n → bool) (tnum n) :=
{ γ                := γ,
  dec_γ            := by { dsimp only [γ], apply_instance },
  abstract         := tnum.const,
  abstract_correct := by apply tnum.const_correct }

instance : abstr_top (fin n → bool) (tnum n) :=
{ top         := ⟨vector.repeat ff _, vector.repeat tt _⟩,
  top_correct := λ _ _ , by {
    simp [vector.nth_repeat],
    refl } }

instance : inhabited (tnum n) := ⟨⊤⟩

protected def join (a b : tnum n) : tnum n :=
let newmask := bv.circuit.or (bv.circuit.xor a.value b.value) (bv.circuit.or a.mask b.mask) in
⟨ vector.map₂ (λ x y, cond x ff y) newmask (bv.circuit.or a.value b.value),
  newmask ⟩

instance : abstr_join (fin n → bool) (tnum n) (tnum n) :=
{ join         := tnum.join,
  join_correct := by {
    intros x y a h i,
    simp only [tnum.join, bv.circuit.nth_xor, bv.circuit.nth_or, bv.or, bv.xor, tnum.rel, vector.nth_map₂,
              cond_eq_or_ands, bnot_eq_true_eq_eq_ff, band_eq_true_eq_eq_tt_and_eq_tt, bool.bnot_band, biff_eq_tt_iff_eq,
              bool.bnot_bor, bor, bool.band_assoc, band_ff, bnot_bnot, bor_eq_true_eq_eq_tt_or_eq_tt],
    cases h; specialize h i;
    simp only [tnum.rel, cond_eq_or_ands, bnot_eq_true_eq_eq_ff, band_eq_true_eq_eq_tt_and_eq_tt, biff_eq_tt_iff_eq,
              bor_eq_true_eq_eq_tt_or_eq_tt] at h; revert h;
    cases (x.mask.nth i); cases (y.mask.nth i); cases (x.value.nth i); cases (y.value.nth i);
      cases (a i); simp } }

protected def meet₁ (value₁ mask₁ value₂ mask₂ : bool) : with_bot (bool × bool) :=
match value₁, mask₁, value₂, mask₂ with
| _, tt, _, tt := some (ff, tt) -- Value unknown in both, still unknown
| _, tt, b, ff := some (b, ff) -- Known in right, meet to known
| a, ff, _, tt := some (a, ff) -- Known in left, meet to known
| a, ff, b, ff := cond (biff a b) (some (a, ff)) ⊥ -- Known in both: if same known, meet to same value, otherwise ⊥.
end

protected def meet : ∀ {n : ℕ} (_ _ : tnum n), with_bot (tnum n)
| 0       _ _ := pure ⟨default _, default _⟩
| (n + 1) a b := do
  bitone ← tnum.meet₁ a.value.head a.mask.head b.value.head b.mask.head,
  bitrest ← meet a.tail b.tail,
  pure $ tnum.cons bitone.1 bitone.2 bitrest

protected theorem meet_correct ⦃x y : tnum n⦄ :
  γ x ∩ γ y ⊆ has_γ.γ (tnum.meet x y) :=
begin
  revert x y,
  induction n with n ih,
  { intros _ _ _ h₁,
    simp only [has_γ.γ, tnum.meet],
    refine fin.elim0 },
  { intros _ _ _ h₁,
    cases h₁ with h₁ h₂,
    rw [γ_iff_head_tail] at h₁ h₂,
    cases h₁ with h₁l h₁r,
    cases h₂ with h₂l h₂r,
    specialize @ih x.tail y.tail (fin.tail a) ⟨h₁r, h₂r⟩,
    simp only [tnum.meet] at ih ⊢,
    cases h₃ : (tnum.meet₁ _ _ _ _),
    case none {
      exfalso,
      cases vector.head x.mask; cases vector.head x.value; cases (a 0); cases h₁l;
      cases vector.head y.mask; cases vector.head y.value; cases (a 0); cases h₂l; cases h₃ },
    case some : v₁ {
      simp only [option.some_bind],
      cases h₄ : x.tail.meet y.tail,
      case none {
        simp only [h₄] at ih,
        cases ih },
      case some : v₂ {
        simp only [option.some_bind, has_γ.γ, pure, with_bot.has_γ._match_1],
        rw [γ_cons_iff],
        simp only [h₄] at ih,
        refine ⟨_, ih⟩,
        clear h₄ ih v₂ h₁r h₂r,
        cases vector.head x.mask; cases vector.head x.value; cases (a 0); cases h₁l;
        cases vector.head y.mask; cases vector.head y.value; cases (a 0); cases h₂l; cases h₃; refl } } }
end

instance : abstr_meet (fin n → bool) (tnum n) (with_bot (tnum n)) :=
{ meet         := tnum.meet,
  meet_correct := by apply tnum.meet_correct }

/--
≤ relation on tnums. This implementation is more complicated than it would otherwise
appear necessary in order to rule out the case where mask i = tt ∧ value i = tt.
-/
protected def subset (a b : tnum n) : Prop :=
∀ (i : fin n),
  (b.value.nth i = ff ∧ b.mask.nth i = tt) ∨
  (a.mask.nth i = ff ∧ b.mask.nth i = ff ∧ a.value.nth i = b.value.nth i)

instance : abstr_le (fin n → bool) (tnum n) :=
{ le := tnum.subset,
  dec_le := by {
    simp only [has_le.le],
    intros _ _,
    dsimp only [tnum.subset],
    apply' fintype.decidable_forall_fintype },
  le_correct := by {
    intros _ _ l _ h i,
    specialize h i,
    specialize l i,
    simp only [tnum.rel] at ⊢ h,
    cases l,
    { simp only [l, cond],
      cases l,
      simp only [bnot_eq_true_eq_eq_ff] },
    { rcases l with ⟨l1, l2, l3⟩,
      simp only [l1, l2, l3, cond] at h,
      simp only [h, l2, cond] } } }


private def lift1 (f : lsbvector n → lsbvector n) (a : tnum n) : tnum n :=
if a.is_const
then ⟨a.mask, f a.value⟩
else ⊤

private theorem lift1_correct
    {f : lsbvector n → lsbvector n}
    {g : (fin n → bool) → fin n → bool}
    (f_nth : ∀ (u : lsbvector n), (f u).nth = g u.nth) :
  ∀ ⦃x : fin n → bool⦄ ⦃a : tnum n⦄,
    x ∈ γ a →
    g x ∈ γ (lift1 f a) :=
begin
  intros _ _ h₁ _,
  simp only [lift1],
  split_ifs with h₃,
  { simp only [γ_is_const h₁ h₃],
    simp only [tnum.is_const] at h₃,
    simp only [h₃, vector.nth_repeat, tnum.rel, cond_eq_or_ands, bnot_eq_true_eq_eq_ff, band_eq_true_eq_eq_tt_and_eq_tt,
               bool.bnot_false, ff_biff, band_tt, bor_eq_true_eq_eq_tt_or_eq_tt, f_nth _, vector.nth_of_fn_ext],
    cases g x i; tauto },
  { have h := @abstr_top.top_correct _ (tnum n) _ _ (g x),
    exact h i }
end

private def lift2 (f : lsbvector n → lsbvector n → lsbvector n) (a b : tnum n) : tnum n :=
if a.is_const ∧ b.is_const
then ⟨a.mask, f a.value b.value⟩
else ⊤

private theorem lift2_correct
    {f : lsbvector n → lsbvector n → lsbvector n}
    {g : (fin n → bool) → (fin n → bool) → fin n → bool}
    (f_nth : ∀ (u v : lsbvector n), (f u v).nth = g u.nth v.nth) :
  ∀ ⦃x y : fin n → bool⦄ ⦃a b : tnum n⦄,
    x ∈ γ a →
    y ∈ γ b →
    g x y ∈ γ (lift2 f a b) :=
begin
  intros _ _ _ _ h₁ h₂ _,
  simp only [lift2],
  split_ifs with h₃,
  { simp only [γ_is_const h₁ h₃.1, γ_is_const h₂ h₃.2],
    rcases h₃ with ⟨h₃, -⟩,
    simp only [tnum.is_const] at h₃,
    simp only [h₃, vector.nth_repeat, rel, cond_eq_or_ands, bnot_eq_true_eq_eq_ff, band_eq_true_eq_eq_tt_and_eq_tt,
               bool.bnot_false, ff_biff, band_tt, bor_eq_true_eq_eq_tt_or_eq_tt, f_nth _ _, vector.nth_of_fn_ext],
    cases g x y i; tauto },
  { have h := @abstr_top.top_correct _ (tnum n) _ _ (g x y),
    exact h i }
end

protected def neg : tnum n → tnum n :=
⊤

protected theorem neg_correct ⦃x : fin n → bool⦄ ⦃a : tnum n⦄ :
  x ∈ γ a →
  -x ∈ γ (tnum.neg a) :=
begin
  intros _,
  apply @abstr_top.top_correct _ (tnum n) _
end

/-- Create the sum of two tnums. -/
-- protected def add (a b : tnum n) : tnum n :=
-- let sm := bv.circuit.add a.mask b.mask,
--     sv := bv.circuit.add a.value b.value,
--     sigma := bv.circuit.add sm sv,
--     chi := bv.circuit.xor sigma sv,
--     mu := bv.circuit.or chi (bv.circuit.or a.mask b.mask) in
--   ⟨bv.circuit.and sv (bv.circuit.not mu), mu⟩

protected def add : tnum n → tnum n → tnum n :=
lift2 bv.circuit.add

protected theorem add_correct ⦃x y : fin n → bool⦄ ⦃a b : tnum n⦄ :
  x ∈ γ a →
  y ∈ γ b →
  x + y ∈ γ (tnum.add a b) :=
by apply lift2_correct (@bv.circuit.nth_add _)

protected def udiv : tnum n → tnum n → tnum n :=
lift2 bv.circuit.udiv

protected theorem udiv_correct ⦃x y : fin n → bool⦄ ⦃a b : tnum n⦄ :
  x ∈ γ a →
  y ∈ γ b →
  x / y ∈ γ (tnum.udiv a b) :=
by apply lift2_correct (@bv.circuit.nth_udiv _)

protected def urem : tnum n → tnum n → tnum n :=
lift2 bv.circuit.urem

protected theorem urem_correct ⦃x y : fin n → bool⦄ ⦃a b : tnum n⦄ :
  x ∈ γ a →
  y ∈ γ b →
  x % y ∈ γ (tnum.urem a b) :=
by apply lift2_correct (@bv.circuit.nth_urem _)

protected def mul : tnum n → tnum n → tnum n :=
lift2 bv.circuit.mul

protected theorem mul_correct ⦃x y : fin n → bool⦄ ⦃a b : tnum n⦄ :
  x ∈ γ a →
  y ∈ γ b →
  x * y ∈ γ (tnum.mul a b) :=
by apply lift2_correct (@bv.circuit.nth_mul _)

/-- Create the bitwise AND of two tnums. -/
protected def and (a b : tnum n) : tnum n :=
let alpha := bv.circuit.or a.value a.mask,
    beta := bv.circuit.or b.value b.mask,
    v := bv.circuit.and a.value b.value in
  ⟨v, bv.circuit.and alpha (bv.circuit.and beta (bv.circuit.not v))⟩

protected theorem and_correct ⦃x y : fin n → bool⦄ ⦃a b : tnum n⦄ :
  x ∈ γ a →
  y ∈ γ b →
  bv.and x y ∈ γ (tnum.and a b) :=
begin
  intros h₁ h₂ i,
  simp only [tnum.and, bv.circuit.nth_and, bv.circuit.nth_not, bv.circuit.nth_or, bv.or, bv.and, bv.not],
  specialize h₁ i,
  specialize h₂ i,
  simp only [tnum.rel, cond_eq_or_ands, bnot_eq_true_eq_eq_ff, band_eq_true_eq_eq_tt_and_eq_tt, bool.bnot_band, biff_eq_tt_iff_eq,
             bool.bnot_bor, band_self, bool.band_assoc, bnot_bnot, bor_eq_true_eq_eq_tt_or_eq_tt] at h₁ h₂ ⊢,
  revert h₁ h₂,
  cases (a.mask.nth i); cases (b.mask.nth i); cases (a.value.nth i); cases (b.value.nth i);
    cases (x i); cases (y i); simp
end

/-- Create the bitwise OR of two tnums. -/
protected def or (a b : tnum n) : tnum n :=
let v := bv.circuit.or a.value b.value,
    mu := bv.circuit.or a.mask b.mask in
  ⟨v, bv.circuit.and mu (bv.circuit.not v)⟩

protected theorem or_correct ⦃x y : fin n → bool⦄ ⦃a b : tnum n⦄ :
  x ∈ γ a →
  y ∈ γ b →
  bv.or x y ∈ γ (tnum.or a b) :=
begin
  intros h₁ h₂ i,
  simp only [tnum.or, bv.circuit.nth_and, bv.circuit.nth_not, bv.circuit.nth_or, bv.or, bv.and, bv.not],
  specialize h₁ i,
  specialize h₂ i,
  simp only [tnum.rel, cond_eq_or_ands, bnot_eq_true_eq_eq_ff, band_eq_true_eq_eq_tt_and_eq_tt, bool.bnot_band, biff_eq_tt_iff_eq,
             bool.bnot_bor, band_self, bool.band_assoc, bnot_bnot, bor_eq_true_eq_eq_tt_or_eq_tt] at h₁ h₂ ⊢,
  revert h₁ h₂,
  cases (a.mask.nth i); cases (b.mask.nth i); cases (a.value.nth i); cases (b.value.nth i);
    cases (x i); cases (y i); simp
end

/-- Create the bitwise XOR of two tnums. -/
protected def xor (a b : tnum n) : tnum n :=
let v := bv.circuit.xor a.value b.value,
    mu := bv.circuit.or a.mask b.mask in
  ⟨bv.circuit.and v (bv.circuit.not mu), mu⟩

theorem xor_correct ⦃x y : fin n → bool⦄ ⦃a b : tnum n⦄ :
  x ∈ γ a →
  y ∈ γ b →
  bv.xor x y ∈ γ (tnum.xor a b) :=
begin
  intros h₁ h₂ i,
  simp only [tnum.xor, bv.circuit.nth_and, bv.circuit.nth_not, bv.circuit.nth_or, bv.circuit.nth_xor, bv.or, bv.and, bv.not, bv.xor],
  specialize h₁ i,
  specialize h₂ i,
  simp only [tnum.rel, cond_eq_or_ands, bnot_eq_true_eq_eq_ff, band_eq_true_eq_eq_tt_and_eq_tt, bool.bnot_band, biff_eq_tt_iff_eq,
             bool.bnot_bor, band_self, bool.band_assoc, bnot_bnot, bor_eq_true_eq_eq_tt_or_eq_tt] at h₁ h₂ ⊢,
  revert h₁ h₂,
  cases (a.mask.nth i); cases (b.mask.nth i); cases (a.value.nth i); cases (b.value.nth i);
    cases (x i); cases (y i); simp
end

instance : bv_abstr n (tnum n) :=
{ neg  := { op := tnum.neg, correct := by { intros, subst_vars, apply tnum.neg_correct; assumption } },
  add  := { op := tnum.add, correct := by { intros, subst_vars, apply tnum.add_correct; assumption } },
  and  := { op := tnum.and, correct := by { intros, subst_vars, apply tnum.and_correct; assumption } },
  or   := { op := tnum.or, correct := by { intros, subst_vars, apply tnum.or_correct; assumption } },
  xor  := { op := tnum.xor, correct := by { intros, subst_vars, apply tnum.xor_correct; assumption } },
  udiv := { op := tnum.udiv, correct := by { intros, subst_vars, apply tnum.udiv_correct; assumption } },
  urem := { op := tnum.urem, correct := by { intros, subst_vars, apply tnum.urem_correct; assumption } },
  mul  := { op := tnum.mul, correct := by { intros, subst_vars, apply tnum.mul_correct; assumption } },
  shl  := { op := λ _ _, ⊤, correct := by { intros, subst_vars, apply @abstr_top.top_correct _ _ _ _ (bv.shl x y) } },
  lshr := { op := λ _ _, ⊤, correct := by { intros, subst_vars, apply @abstr_top.top_correct _ _ _ _ (bv.lshr x y) } },
  ashr := { op := λ _ _, ⊤, correct := by { intros, subst_vars, apply @abstr_top.top_correct _ _ _ _ (bv.ashr x y) } },
  lt   := abstr_binary_inversion.trivial,
  eq   := abstr_meet.invert_equality }

end tnum
