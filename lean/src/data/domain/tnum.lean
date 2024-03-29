/-
Copyright (c) 2021 The UNSAT Group. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luke Nelson, Xi Wang
-/
import .basic
import .bv
import .trit
import data.bv.adc
import data.bv.mul
import data.bv.sbc
import data.bv.circuit
import misc.vector

/-!
# Tristate numbers (tnum)

A tristate number (tnum) overapproximates the set of values that a variable may take at the bit
level. Each bit of a variable may be either 0, 1, or unknown.

## Implementation notes

An earlier implementation represents each tnum as a pair of (value, mask), where the i-th bit of
the mask indicates whether the corresponding bit is known (0/1, as the i-th bit of the value) or
unknown. This is similar to the representation used by the Linux kernel. This complicates both
implementation and proof in Lean. We therefore switch to the current implementation.

## References

* Harishankar Vishwanathan, Matan Shachnai, Srinivas Narayana, and Santosh Nagarakatte.
  *Semantics, Verification, and Efficient Implementations for Tristate Numbers*.
  <https://arxiv.org/abs/2105.05398>
-/

axiom bogus : false

/-- A tnum is a vector trits. -/
@[reducible]
def tnum (n : ℕ) := vector trit n

namespace tnum
variables {n m : ℕ}
open has_γ

private def repr' : Π {n : ℕ}, tnum n → string
| 0       _ := ""
| (n + 1) v :=
  let x := match v.head with
           | some ff := "0"
           | some tt := "1"
           | unknown := "x"
           end in
    x ++ @repr' n v.tail

instance : has_repr (tnum n) := ⟨λ v, "0b" ++ repr' v.reverse⟩

/-- Concretization function. Relates tnums to sets of bitvectors. -/
protected def γ (t : tnum n) : set (fin n → bool) :=
λ (v : fin n → bool), ∀ (i : fin n), v i ∈ γ (t.nth i)

local attribute [reducible] tnum.γ

instance : has_γ (fin n → bool) (tnum n) :=
{ γ := tnum.γ }

instance : has_decidable_γ (fin n → bool) (tnum n) :=
{ dec_γ := by {
    intros x y,
    apply @fintype.decidable_forall_fintype _ _ _,
    intros i,
    apply_instance } }

/-- Cast a constant to a tnum. -/
protected def const (v : fin n → bool) : abstr_nullary_relation (= v) (tnum n) :=
{ op      := vector.of_fn $ λ i, (with_top.lift_nullary_relation (id.const (v i))).op,
  correct := by {
    intros _ h i,
    subst h,
    simp only [vector.nth_of_fn],
    apply (with_top.lift_nullary_relation _).correct rfl } }

/-- A tnum is constant iff every trit in it is constant. -/
protected def is_const (x : tnum n) :=
∀ (i : fin n), (x.nth i).is_const

local attribute [reducible] tnum.is_const

instance : decidable_pred (tnum.is_const : tnum n → Prop) := infer_instance

/--
Cast a tnum to a vector of constant bools.
If each trit in the tnum was constant, then the result will be the single
value the tnum can take on. Maps to vector rather than fin n → bool so that
operations can be efficiently performed on the result.
-/
protected def to_const (x : tnum n) : vector bool n :=
x.map trit.to_const

/-- to_const returns a correct value if the input tnum is constant. -/
protected theorem to_const_γ {x : tnum n} :
  x.is_const →
  ∀ (b : fin n → bool),
    b ∈ γ x →
    x.to_const = vector.of_fn b :=
begin
  intros h₁ b h₂,
  ext i,
  have h₃ := trit.to_const_γ (h₁ i) (b i) (h₂ i),
  simp only [vector.nth_of_fn, ← h₃, tnum.to_const, vector.nth_map]
end

instance : abstr_top (fin n → bool) (tnum n) :=
{ top         := vector.repeat ⊤ n,
  top_correct := by {
    intros _ i,
    simp only [vector.nth_repeat] } }

/-- Create the join of two tnums. -/
protected def join : tnum n → tnum n → tnum n :=
vector.map₂ (⊔)

instance : abstr_join (fin n → bool) (tnum n) (tnum n) :=
{ join         := tnum.join,
  join_correct := by {
    intros x y u h i,
    cases h;
      simp only [tnum.join, vector.nth_map₂];
      apply abstr_join.join_correct,
    { left, exact h i },
    { right, exact h i } } }

/-- Create the meet of two tnums. -/
protected def meet (x y : tnum n) : with_bot (tnum n) :=
let x : with_bot (flip vector n trit) := sequence (vector.map₂ abstr_meet.meet x y : flip vector n (with_bot trit)) in x

instance : abstr_meet (fin n → bool) (tnum n) (with_bot (tnum n)) :=
{ meet         := tnum.meet,
  meet_correct := by {
    induction n with n ih,
    { intros _ _ _ _,
      rw [vector.eq_nil x, vector.eq_nil y],
      refine fin.elim0 },
    { rintros x y u ⟨h₁, h₂⟩,
      rw [← vector.cons_head_tail x, ← vector.cons_head_tail y],
      simp only [tnum.meet, vector.map₂_cons],
      cases h₃ : (abstr_meet.meet (vector.head x) (vector.head y)),
      case none {
        have h₄ := abstr_meet.meet_correct ⟨h₁ 0, h₂ 0⟩,
        simp only [vector.nth_zero] at h₄,
        rw [h₃] at h₄,
        cases h₄ },
      case some : tr {
        specialize @ih x.tail y.tail (fin.tail u) _,
        { split,
          { intros i,
            simp only [vector.nth_tail_succ],
            exact h₁ i.succ },
          { intros i,
            simp only [vector.nth_tail_succ],
            exact h₂ i.succ } },
        simp only [tnum.meet] at ih,
        simp only [sequence, traverse, option.map_some', id.def, option.map_eq_map, vector.traverse_def, has_seq.seq, option.some_bind'] at ⊢ ih,
        cases h₅ : vector.traverse id _,
        case none {
          rw [h₅] at ih,
          cases ih },
        case some {
          rw [h₅] at ih,
          simp only [option.map_some'],
          intros i,
          refine fin.cases _ _ i,
          { have h₆ := abstr_meet.meet_correct ⟨h₁ 0, h₂ 0⟩,
            simp only [vector.nth_zero] at h₆,
            rw [h₃] at h₆,
            simp only [vector.nth_cons_zero],
            exact h₆,
            exact (with_bot trit),
            apply_instance,
            apply_instance },
          { intros j,
            simp only [vector.nth_cons_succ],
            exact ih j } } } } } }

/-- Less-equal of two tnums is defined over each trit. -/
protected def le (a b : tnum n) : Prop :=
∀ (i : fin n), a.nth i ≤ b.nth i

instance : abstr_le (fin n → bool) (tnum n) :=
{ le     := tnum.le,
  dec_le := by {
    intros _ _,
    simp only [tnum.le],
    apply_instance },
  le_correct := by {
    intros x y l u h i,
    apply abstr_le.le_correct (l i) (h i) } }

/-- Create the bitwise NOT of a tnums. -/
protected def not : tnum n → tnum n :=
vector.map trit.not.op

theorem not_correct ⦃x : fin n → bool⦄ ⦃a : tnum n⦄ :
  x ∈ γ a →
  bv.not x ∈ γ (tnum.not a) :=
begin
  intros h₁ i,
  simp only [tnum.not, vector.nth_map],
  apply trit.not.correct (h₁ i) rfl
end

section add

/-- Create the addition-with-carry of two tnums. -/
protected def adc : ∀ {n : ℕ}, tnum n → tnum n → trit → tnum n
| 0       _ _ carry := vector.nil
| (n + 1) a b carry :=
  let c  : (trit × trit) := trit.full_add a.head b.head carry,
      cs : tnum n        := @adc n a.tail b.tail c.2 in
    c.1 ::ᵥ cs

protected theorem adc_correct {n : ℕ} {a b : tnum n} {c : trit} {x y : fin n → bool} {z : bool} :
  x ∈ γ a →
  y ∈ γ b →
  z ∈ γ c →
  bv.adc x y z ∈ γ (tnum.adc a b c) :=
begin
  induction n with n ih generalizing a b c x y z,
  case zero {
    intros _ _ _,
    refine fin.elim0 },
  case succ {
    intros h₁ h₂ h₃,
    specialize @ih a.tail b.tail (trit.full_add a.head b.head c).2 (fin.tail x) (fin.tail y) (bool.full_add (x 0) (y 0) z).2 _ _ _,
    { intros i,
      simp only [vector.nth_tail_succ],
      exact h₁ i.succ },
    { intros i,
      simp only [vector.nth_tail_succ],
      exact h₂ i.succ },
    { simp only [← vector.nth_zero],
      exact (trit.full_add_correct (h₁ 0) (h₂ 0) h₃).2 },
    simp only [tnum.adc],
    intros i,
    refine fin.cases _ _ i,
    { simp only [bv.adc_zero, vector.nth_cons_zero, ← vector.nth_zero],
      exact (trit.full_add_correct (h₁ 0) (h₂ 0) h₃).1 },
    { intros j,
      simp only [bv.adc_succ, vector.nth_cons_succ],
      exact ih j } }
end

/-- Create the addition of two tnums. -/
protected def add (a b : tnum n) : tnum n :=
tnum.adc a b (some ff)

protected theorem add_correct ⦃x y : fin n → bool⦄ ⦃a b : tnum n⦄ :
  x ∈ γ a →
  y ∈ γ b →
  x + y ∈ γ (tnum.add a b) :=
begin
  intros h₁ h₂,
  simp only [bv.add_eq_adc],
  apply tnum.adc_correct h₁ h₂,
  dec_trivial
end

end add

section and

/-- Create the bitwise AND of two tnums. -/
protected def and : tnum n → tnum n → tnum n :=
vector.map₂ trit.and.op

protected theorem and_correct ⦃x y : fin n → bool⦄ ⦃a b : tnum n⦄ :
  x ∈ γ a →
  y ∈ γ b →
  bv.and x y ∈ γ (tnum.and a b) :=
begin
  intros h₁ h₂ i,
  simp only [tnum.and, vector.nth_map₂],
  apply trit.and.correct (h₁ i) (h₂ i) rfl
end

end and

section mul

/-- Create the multiplication of two tnums. -/
protected def mul : ∀ {n : ℕ}, tnum n → tnum n → tnum n
| 0       _ _ := vector.nil
| (n + 1) a b :=
  let p := tnum.and a (vector.repeat b.head _),
      r := @mul n a.init b.tail,
      s := tnum.add p.tail r in
  p.head ::ᵥ s

protected theorem mul_correct ⦃x y : fin n → bool⦄ ⦃a b : tnum n⦄ :
  x ∈ γ a →
  y ∈ γ b →
  x * y ∈ γ (tnum.mul a b) :=
begin
  induction n with n ih generalizing a b x y,
  case zero {
    intros _ _,
    refine fin.elim0 },
  case succ {
    intros h₁ h₂,
    specialize @ih a.init b.tail (fin.init x) (fin.tail y) _ _,
    { intros i,
      simp only [vector.nth_init, fin.coe_eq_cast_succ],
      exact h₁ _, },
    { intros i,
      simp only [vector.nth_tail_succ],
      exact h₂ i.succ },
    simp only [tnum.mul],
    intros i,
    refine fin.cases _ _ i,
    { simp only [bv.mul_head, vector.nth_cons_zero, ← vector.nth_zero, tnum.and, vector.nth_map₂],
      refine trit.and.correct (h₁ 0) _ rfl,
      simp only [vector.nth_repeat],
      exact h₂ 0 },
    { intros j,
      change (x * y) j.succ with fin.tail (x * y) j,
      simp only [bv.mul_tail, vector.nth_cons_succ],
      apply tnum.add_correct _ ih j,
      intros j,
      simp only [fin.tail, vector.nth_tail_succ, tnum.and, vector.nth_map₂],
      refine trit.and.correct (h₁ j.succ) _ rfl,
      simp only [vector.nth_repeat, ← vector.nth_zero],
      exact h₂ 0 } }
end

end mul

section neg

/-- Create the negation of two tnums. -/
protected def neg (a : tnum n) : tnum n :=
tnum.add (tnum.not a) (tnum.const 1).op

protected theorem neg_correct ⦃x : fin n → bool⦄ ⦃a : tnum n⦄ :
  x ∈ γ a →
  -x ∈ γ (tnum.neg a) :=
begin
  intros h₁,
  simp only [bv.neg_eq_not_add_one, tnum.neg],
  apply tnum.add_correct,
  { apply tnum.not_correct h₁ },
  { apply (tnum.const _).correct rfl }
end

end neg

section sub

/-- Create the subtraction of two tnums. -/
protected def sub (a b : tnum n) : tnum n :=
tnum.adc a (tnum.not b) (some tt)

protected theorem sub_correct ⦃x y : fin n → bool⦄ ⦃a b : tnum n⦄ :
  x ∈ γ a →
  y ∈ γ b →
  x - y ∈ γ (tnum.sub a b) :=
begin
  intros h₁ h₂,
  rw [bv.sub_eq_sbc, bv.sbc_eq_adc],
  apply tnum.adc_correct h₁ (tnum.not_correct h₂),
  dec_trivial
end

end sub

/-- If inputs are constant, use circuit implementation of udiv, otherwise ⊤. -/
protected def udiv (a b : tnum n) : tnum n :=
if a.is_const ∧ b.is_const
then vector.map some $ bv.circuit.udiv a.to_const b.to_const
else ⊤

protected theorem udiv_correct ⦃x y : fin n → bool⦄ ⦃a b : tnum n⦄ :
  x ∈ γ a →
  y ∈ γ b →
  x / y ∈ γ (tnum.udiv a b) :=
begin
  intros h₁ h₂,
  simp only [tnum.udiv],
  split_ifs,
  { intros i,
    simp only [vector.nth_map, bv.circuit.nth_udiv, tnum.to_const_γ h.1 x h₁, tnum.to_const_γ h.2 y h₂, vector.nth_of_fn_ext],
    exact rfl },
  { apply abstr_top.top_correct _ }
end

/-- If inputs are constant, use circuit implementation of urem, otherwise ⊤. -/
protected def urem (a b : tnum n) : tnum n :=
if a.is_const ∧ b.is_const
then vector.map some $ bv.circuit.urem a.to_const b.to_const
else ⊤

protected theorem urem_correct ⦃x y : fin n → bool⦄ ⦃a b : tnum n⦄ :
  x ∈ γ a →
  y ∈ γ b →
  x % y ∈ γ (tnum.urem a b) :=
begin
  intros h₁ h₂,
  simp only [tnum.urem],
  split_ifs,
  { intros i,
    simp only [vector.nth_map, bv.circuit.nth_urem, tnum.to_const_γ h.1 x h₁, tnum.to_const_γ h.2 y h₂, vector.nth_of_fn_ext],
    exact rfl },
  { apply abstr_top.top_correct _ }
end

/-- Create the bitwise OR of two tnums. -/
protected def or : tnum n → tnum n → tnum n :=
vector.map₂ trit.or.op

protected theorem or_correct ⦃x y : fin n → bool⦄ ⦃a b : tnum n⦄ :
  x ∈ γ a →
  y ∈ γ b →
  bv.or x y ∈ γ (tnum.or a b) :=
begin
  intros h₁ h₂ i,
  simp only [tnum.or, vector.nth_map₂],
  apply trit.or.correct (h₁ i) (h₂ i) rfl
end

/-- Create the bitwise XOR of two tnums. -/
protected def xor : tnum n → tnum n → tnum n :=
vector.map₂ trit.xor.op

theorem xor_correct ⦃x y : fin n → bool⦄ ⦃a b : tnum n⦄ :
  x ∈ γ a →
  y ∈ γ b →
  bv.xor x y ∈ γ (tnum.xor a b) :=
begin
  intros h₁ h₂ i,
  simp only [tnum.xor, vector.nth_map₂],
  apply trit.xor.correct (h₁ i) (h₂ i) rfl
end

section shl

/-- Shift left by a constant. -/
private def shiftl (a : tnum n) (amt : ℕ) : tnum n :=
by {
  convert (vector.repeat (some ff) (min n amt)).append (a.take (n - amt)),
  simp only [add_comm, min_eq_left (nat.sub_le _ _), nat.sub_add_min_cancel] }

private theorem shiftl_correct {a : tnum n} {amt : ℕ} {x : fin n → bool} :
  x ∈ γ a →
  bv.of_nat ((bv.to_nat x) * 2^amt) ∈ γ (shiftl a amt) :=
begin
  intros h₁,
  exact bogus.elim
end

private def shl_aux : ℕ → tnum n → Π {m : ℕ}, tnum m → tnum n
| amt a 0       _ := a
| amt a (m + 1) b :=
  let a' := match b.head with
            | some ff := a
            | some tt := shiftl a amt
            | none    := a ⊔ shiftl a amt
            end
  in @shl_aux (nat.shiftl amt 1) a' m b.tail

private theorem shl_aux_correct (amt : ℕ) {a : tnum n} {m : ℕ} {b : tnum m} {x : fin n → bool} {y : fin m → bool} :
  x ∈ γ a →
  y ∈ γ b →
  bv.shl x (bv.of_nat (bv.to_nat y * amt) : fin m → bool) ∈ γ (shl_aux amt a b) :=
begin
  induction m with m' ih generalizing a x b y n amt,
  case zero {
    intros h₁ h₂,
    change y with 0,
    simp only [shl_aux, bv.to_nat_zero, bv.shl, mul_one, bv.of_to_nat, pow_zero],
    exact h₁ },
  case succ {
    intros h₁ h₂,
    have h₂' : fin.tail y ∈ γ b.tail,
    { intros i,
      simp only [fin.tail, vector.nth_tail_succ],
      exact h₂ i.succ },
    have ih₂ := @ih,
    specialize @ih n (nat.shiftl amt 1) a b.tail x (fin.tail y) h₁ h₂',
    specialize @ih₂ n (nat.shiftl amt 1) (shiftl a amt) b.tail _ (fin.tail y) (shiftl_correct h₁) h₂',
    simp only [shl_aux, bv.to_nat_tail, nat.shiftl_eq_mul_pow] at ih ih₂ ⊢,
    exact bogus.elim }
end

protected def shl (a : tnum n) (b : tnum m) : tnum n :=
shl_aux 1 a b

theorem shl_correct ⦃x : fin n → bool⦄ ⦃y : fin m → bool⦄ ⦃a : tnum n⦄ ⦃b : tnum m⦄ :
  x ∈ γ a →
  y ∈ γ b →
  bv.shl x y ∈ γ (tnum.shl a b) :=
begin
  intros h₁ h₂,
  have h₃ := shl_aux_correct 1 h₁ h₂,
  simp only [mul_one, bv.of_to_nat] at h₃,
  exact h₃
end

end shl

protected def lshr (a : tnum n) (b : tnum m) : tnum n :=
⊤

theorem lshr_correct ⦃x : fin n → bool⦄ ⦃y : fin m → bool⦄ ⦃a : tnum n⦄ ⦃b : tnum m⦄ :
  x ∈ γ a →
  y ∈ γ b →
  bv.lshr x y ∈ γ (tnum.lshr a b) :=
begin
  intros h₁ h₂,
  apply abstr_top.top_correct _
end

protected def ashr (a : tnum n) (b : tnum m) : tnum n :=
⊤

theorem ashr_correct ⦃x : fin n → bool⦄ ⦃y : fin m → bool⦄ ⦃a : tnum n⦄ ⦃b : tnum m⦄ :
  x ∈ γ a →
  y ∈ γ b →
  bv.ashr x y ∈ γ (tnum.ashr a b) :=
begin
  intros h₁ h₂,
  apply abstr_top.top_correct _
end

instance : abstr_bv tnum :=
{ to_has_γ := λ _, infer_instance,
  to_has_decidable_γ := λ _, infer_instance,
  to_abstr_le := λ _, infer_instance,
  to_abstr_top := λ _, infer_instance,
  to_abstr_meet := λ _, infer_instance,
  to_abstr_join := λ _, infer_instance,
  const := λ _, tnum.const,
  neg  := λ _, { op := tnum.neg, correct := by { intros, subst_vars, apply tnum.neg_correct; assumption } },
  not  := λ _, { op := tnum.not, correct := by { intros, subst_vars, apply tnum.not_correct; assumption } },
  add  := λ _, { op := tnum.add, correct := by { intros, subst_vars, apply tnum.add_correct; assumption } },
  sub  := λ _, { op := tnum.sub, correct := by { intros, subst_vars, apply tnum.sub_correct; assumption } },
  and  := λ _, { op := tnum.and, correct := by { intros, subst_vars, apply tnum.and_correct; assumption } },
  or   := λ _, { op := tnum.or, correct := by { intros, subst_vars, apply tnum.or_correct; assumption } },
  xor  := λ _, { op := tnum.xor, correct := by { intros, subst_vars, apply tnum.xor_correct; assumption } },
  udiv := λ _, { op := tnum.udiv, correct := by { intros, subst_vars, apply tnum.udiv_correct; assumption } },
  urem := λ _, { op := tnum.urem, correct := by { intros, subst_vars, apply tnum.urem_correct; assumption } },
  mul  := λ _, { op := tnum.mul, correct := by { intros, subst_vars, apply tnum.mul_correct; assumption } },
  shl  := λ _ _, { op := tnum.shl, correct := by { intros, subst_vars, apply tnum.shl_correct; assumption } },
  lshr := λ _ _, { op := tnum.lshr, correct := by { intros, subst_vars, apply tnum.lshr_correct; assumption } },
  ashr := λ _ _, { op := tnum.ashr, correct := by { intros, subst_vars, apply tnum.ashr_correct; assumption } } }

section optimality
variables (f : tnum n → tnum n → tnum n) (g : (fin n → bool) → (fin n → bool) → fin n → bool)

private def correct : Prop :=
  ∀ {x y u v}, x ∈ γ u → y ∈ γ v → g x y ∈ γ (f u v)

/-
A binary tnum operator "f" is optimal iff for any other correct operator "f'",
f is a subset of f' on all inputs.
-/
private def optimal : Prop :=
  ∀ (f' : tnum n → tnum n → tnum n),
    correct f' g →
    ∀ u v, γ (f u v) ⊆ γ (f' u v)

/-
This is the property we actually check in Rosette.
-/
private def rosette_formulation : Prop :=
  ∀ (a b d : tnum n) (z : fin n → bool),
    z ∈ γ (f a b) →
    z ∉ γ d →
    ∃ (x y : fin n → bool),
      x ∈ γ a ∧ y ∈ γ b ∧ g x y ∉ γ d

/-
The rosette formulation of optimality is equivalent to the natural definition
that quantifies over functions.
-/
private theorem rosette_formulation_ok : rosette_formulation f g ↔ optimal f g :=
begin
  simp only [optimal, rosette_formulation],
  split,
  { intros h₁ f' f'_correct u v z h₂,
    specialize h₁ u v (f' u v) z h₂,
    contrapose! h₁,
    split, exact h₁,
    simp only [correct] at f'_correct,
    intros x y,
    apply f'_correct },
  { intros h₁ a b d z h₂ h₀,
    contrapose! h₀,
    specialize h₁ (λ u v, if a = u ∧ b = v then d else ⊤) _,
    { simp only [correct],
      intros _ _ _ _ _ _,
      split_ifs,
      cases h,
      subst_vars,
      specialize h₀ x y,
      apply h₀; assumption,
      apply abstr_top.top_correct _ },
    { specialize h₁ a b h₂,
      convert h₁,
      simp only [if_true, eq_self_iff_true, and_self] } }
end

end optimality
end tnum
