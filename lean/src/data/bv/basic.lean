/-
Copyright (c) 2021 The UNSAT Group. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luke Nelson, Xi Wang
-/
import data.nat.bitwise
import data.zmod.basic
import tactic.omega.main
import tactic.ring_exp
import misc.list

/-!
# Fixed-size bitvectors

This file defines fixed-sized bitvectors following the SMT-LIB standard.

## Implementation notes

* `fin n → bool` is chosen as the data type, as it doesn't assume the order of bits.

* Map `fin n → bool` to `fin (2^n)` to reuse its theorems, as the latter forms a commutative ring.

## References

* http://smtlib.cs.uiowa.edu/Theories/FixedSizeBitVectors.smt2
* http://smtlib.cs.uiowa.edu/Logics/QF_BV.smt2
-/

localized "attribute [instance] fin.comm_ring fin.has_neg" in fin

open_locale fin

namespace bv

section repr
variable {n : ℕ}

instance : has_repr (fin n → bool) :=
⟨λ v, "0b" ++ ⟨(list.of_fn (λ i, cond (v i) '1' '0')).reverse⟩⟩

end repr

section conversion
variable {n : ℕ}

/-- Convert bit-vector to nat. -/
def to_nat (v : fin n → bool) : ℕ :=
(list.of_fn (λ i, cond (v i) 1 0 * 2^(i : ℕ))).sum

lemma to_nat_cons (b : bool) (v : fin n → bool) :
  to_nat (fin.cons b v) = (to_nat v).bit b :=
begin
  rw [to_nat, nat.bit_val],
  suffices : (list.of_fn (λ i, cond (v i) 1 0 * 2^(↑i + 1))).sum = 2 * to_nat v,
  by simpa [add_comm],
  rw to_nat,
  have h : ∀ (l : list ℕ) (r : ℕ), (l.map (λ b, r * b)).sum = r * l.sum,
  { intros L r,
    have h' := list.sum_map_mul_left L id r,
    simp only [list.map_id] at h'; assumption },
  rw [← h, list.map_of_fn], congr,
  ext i, rw function.comp_app, ring_exp
end

lemma to_nat_snoc (v : fin n → bool) (b : bool) :
  to_nat (fin.snoc v b) = to_nat v + 2^n * cond b 1 0 :=
begin
  induction n with n ih,
  { simp [to_nat, fin.snoc] },
  { rw ← fin.cons_self_tail v,
    rw ← fin.cons_snoc_eq_snoc_cons,
    repeat { rw [to_nat_cons, nat.bit_val] },
    rw [ih], ring_exp }
end

lemma to_nat_succ (v : fin n.succ → bool) :
  to_nat v = (to_nat (fin.tail v)).bit (v 0) :=
begin
  conv_lhs { rw ← fin.cons_self_tail v },
  apply to_nat_cons
end

@[simp]
lemma pow_two_sub_add_cancel :
  2^n - 1 + 1 = 2^n :=
begin
  rw nat.sub_add_cancel,
  apply one_le_pow_of_one_le,
  dec_trivial
end

@[simp]
lemma pow_two_succ_sub_add_cancel :
  2^n.succ - 2 + 1 = 2^n.succ - 1 :=
begin
  rw ← nat.sub_sub_assoc; try { dec_trivial },
  rw pow_succ,
  apply nat.le_mul_of_pos_right,
  apply pow_pos, dec_trivial
end

lemma to_nat_le (v : fin n → bool) :
  to_nat v ≤ 2^n - 1 :=
begin
  induction n with n ih,
  { refl },
  { calc to_nat v
        = 2 * to_nat (fin.tail v) + cond (v 0) 1 0 : by rw [to_nat_succ, nat.bit_val]
    ... ≤ 2 * (2^n - 1) + 1 : by { mono, { mono; dec_trivial }, { cases (v 0); dec_trivial } }
    ... = 2^n.succ - 2 + 1 : by rw [pow_succ, nat.mul_sub_left_distrib, mul_one]
    ... = 2^n.succ - 1 : by simp }
end

lemma to_nat_lt (v : fin n → bool) :
  to_nat v < 2^n :=
calc to_nat v
    ≤ 2^n - 1 : to_nat_le _
... < 2^n : nat.sub_lt (pow_pos dec_trivial _) dec_trivial

@[simp]
lemma to_nat_zero (v : fin 0 → bool) :
  to_nat v = 0 :=
by simp [to_nat]

lemma to_nat_init (v : fin (n + 1) → bool) :
  to_nat (fin.init v) = to_nat v % 2^n :=
begin
  conv_rhs { rw ← fin.snoc_init_self v },
  rw [to_nat_snoc, nat.add_mul_mod_self_left, nat.mod_eq_of_lt],
  apply to_nat_lt
end

lemma to_nat_tail (v : fin (n + 1) → bool) :
  to_nat (fin.tail v) = (to_nat v).div2 :=
begin
  conv_rhs { rw ← fin.cons_self_tail v },
  rw [to_nat_cons, nat.div2_bit]
end

/-- Convert an `n`-bit bitvector to `fin (2^n)`.

This enables the reuse of ring theorems on `fin (2^n)`.

Don't use `fin (2^n)` directly. Use `fin (2^n - 1 + 1)` to match `fin.comm_string` in `data.zmod`,
which is defined on `fin (_ + 1)`.
-/
def to_fin (v : fin n → bool) : fin (2^n - 1 + 1) :=
⟨to_nat v, nat.lt_succ_of_le (to_nat_le _) ⟩

/-- Convert nat to bit-vector -/
def of_nat (a : ℕ) : fin n → bool :=
λ i, a.test_bit i

@[simp]
theorem of_to_nat (v : fin n → bool) :
  of_nat (to_nat v) = v :=
begin
  ext ⟨i, h⟩, revert i h,
  induction n with n ih; intros i h,
  { exact (nat.not_lt_zero _).elim h },
  { rw to_nat_succ,
    cases i; simp [of_nat, fin.coe_mk],
    rw nat.test_bit_succ,
    apply ih,
    omega }
end

theorem to_nat_inj (v₁ v₂ : fin n → bool) :
  to_nat v₁ = to_nat v₂ ↔ v₁ = v₂ :=
⟨λ h, function.left_inverse.injective of_to_nat h, congr_arg _⟩

theorem eq_of_to_nat_eq_to_nat {v₁ v₂ : fin n → bool} :
  to_nat v₁ = to_nat v₂ → v₁ = v₂ :=
(to_nat_inj v₁ v₂).1

theorem eq_of_to_fin_eq_to_fin {v₁ v₂ : fin n → bool} :
  to_fin v₁ = to_fin v₂ → v₁ = v₂ :=
begin
  intro h,
  apply eq_of_to_nat_eq_to_nat,
  finish [to_fin]
end

theorem to_nat_eq_of_heq {n₁ n₂ : ℕ} {v₁ : fin n₁ → bool} {v₂ : fin n₂ → bool} :
  n₁ = n₂ →
  v₁ == v₂ →
  to_nat v₁ = to_nat v₂ :=
begin
  intros h₁ h₂, subst h₁,
  rw heq_iff_eq at h₂,
  subst h₂
end

lemma of_nat_succ (a : ℕ) :
  (of_nat a : fin n.succ → bool) = fin.cons a.bodd (of_nat a.div2) :=
begin
  ext ⟨i, h⟩,
  cases i,
  { refl },
  { rw ← fin.succ; try { omega },
    rw fin.cons_succ,
    conv_lhs { rw ← nat.bit_decomp a },
    apply nat.test_bit_succ }
end

lemma to_of_nat : ∀ (a : ℕ),
  to_nat (@of_nat n a) = a % 2^n :=
begin
  induction n with n ih; intro a,
  { rw [pow_zero, nat.mod_one],
    refl },
  { rw [of_nat_succ, to_nat_succ, fin.cons_zero, fin.tail_cons],
    rw [ih, @nat.mod_pow_succ 2 dec_trivial],
    rw [nat.bit_val, nat.mod_two_of_bodd, nat.div2_val] }
end

theorem of_nat_iff_modeq (a b : ℕ) : @of_nat n a = of_nat b ↔ a ≡ b [MOD 2^n] :=
begin
  rw ← to_nat_inj,
  simp only [to_of_nat],
  refl
end

/-- Extract the most-significant bit.

It returns `ff` for bitvectors of width zero to make other functions simpler.
-/
@[reducible]
def msb : ∀ {n : ℕ}, (fin n → bool) → bool
| 0       _ := ff
| (n + 1) v := v (fin.last n)

end conversion

/-! ### Consants -/
section const
variable {n : ℕ}

instance : has_bot (fin n → bool) :=
⟨λ _, ff⟩

instance : has_top (fin n → bool) :=
⟨λ _, tt⟩

instance : has_zero (fin n → bool) :=
⟨λ _, ff⟩

instance : has_one (fin n → bool) :=
⟨λ i, if i.1 = 0 then tt else ff⟩

lemma bot_to_nat :
  to_nat (⊥ : fin n → bool) = 0 :=
begin
  induction n with n ih,
  { finish [to_nat] },
  { rw to_nat_succ,
    simp only [nat.bit_eq_zero],
    split; try { refl },
    apply ih }
end

lemma top_to_nat :
  to_nat (⊤ : fin n → bool) = 2^n - 1 :=
begin
  induction n with n ih,
  { finish [to_nat] },
  { rw to_nat_succ,
    rw nat.bit_val,
    have h : 2^n.succ - 1 = 2 * (2^n - 1) + 1,
    calc 2^n.succ - 1
        = 2^n.succ - 2 + 1 : by simp
    ... = 2 * (2^n - 1) + 1 : by rw [pow_succ, nat.mul_sub_left_distrib, mul_one],
    rw h, congr, apply ih }
end

lemma zero_to_nat :
  to_nat (0 : fin n → bool) = 0 :=
bot_to_nat

lemma zero_to_fin :
  to_fin (0 : fin n → bool) = 0 :=
begin
  dunfold to_fin, congr,
  apply zero_to_nat
end

lemma one_to_nat :
  to_nat (1 : fin (n + 1) → bool) = 1 :=
begin
  rw to_nat_succ,
  have h : fin.tail (1 : fin (n + 1) → bool) = 0,
  { ext ⟨i, h⟩, refl },
  rw [h, zero_to_nat], refl
end

lemma one_to_fin :
  to_fin (1 : fin n → bool) = 1 :=
begin
  dunfold to_fin, congr,
  cases n; try { refl },
  rw [← pow_two_succ_sub_add_cancel, nat.one_mod],
  apply one_to_nat
end

end const

/-! ### Bitwise operators

Bitwise operators are connected to `boolean_algebra`, as follows:

* `pi.boolean_algebra` provides `boolean_algebra (fin n → bool)` given `boolean_algebra bool`.

* `boolean_algebra bool` builds on `distribounded_distrib_latticeb_lattice bool`, which explicitly
   provides definitions of `sup` and `inf` rather than reusing `distrib_lattice_of_linear_order`
   with `linear_order bool`.

Doing so provides definitional equality between `bv.not`, `bv.and`, `bv.or` and `ᶜ`, `⊓`, `⊔`,
respectively, simplifying the reuse of the theorems on boolean algebra.
-/
section bitwise
variable {n : ℕ}

/-- Bitwise `not`. -/
protected def not (v : fin n → bool) : fin n → bool :=
λ i, !v i

/-- Bitwise `and`. -/
protected def and (v₁ v₂ : fin n → bool) : fin n → bool :=
λ i, v₁ i && v₂ i

/-- Bitwise `or`. -/
protected def or (v₁ v₂ : fin n → bool) : fin n → bool :=
λ i, v₁ i || v₂ i

/-- Bitwise `xor`. -/
protected def xor (v₁ v₂ : fin n → bool) : fin n → bool :=
λ i, bxor (v₁ i) (v₂ i)

instance : has_compl (fin n → bool) :=
⟨bv.not⟩

instance : has_inf (fin n → bool) :=
⟨bv.and⟩

instance : has_sup (fin n → bool) :=
⟨bv.or⟩

instance : bounded_distrib_lattice bool :=
{ sup          := bor,
  le_sup_left  := dec_trivial,
  le_sup_right := dec_trivial,
  sup_le       := dec_trivial,

  inf          := band,
  inf_le_left  := dec_trivial,
  inf_le_right := dec_trivial,
  le_inf       := dec_trivial,
  le_sup_inf   := dec_trivial,

  top          := tt,
  le_top       := dec_trivial,

  bot          := ff,
  bot_le       := dec_trivial,

  .. (_ : partial_order bool) }

instance : boolean_algebra bool :=
{ compl            := bnot,
  sdiff            := λ a b, a && !b,
  sdiff_eq         := dec_trivial,
  sup_inf_sdiff    := dec_trivial,
  inf_inf_sdiff    := dec_trivial,
  inf_compl_le_bot := dec_trivial,
  top_le_sup_compl := dec_trivial,
  .. (_ : bounded_distrib_lattice bool) }

instance : boolean_algebra (fin n → bool) :=
{ sup   := (⊔),
  inf   := (⊓),
  compl := λ v, vᶜ,
  top   := ⊤,
  bot   := ⊥,
  .. (_ : boolean_algebra (fin n → bool)) }

theorem not_to_nat (v : fin n → bool) :
  to_nat (bv.not v) = 2^n - 1 - to_nat v :=
begin
  suffices : to_nat (bv.not v) + to_nat v + 1 = 2^n, by omega,
  induction n with n ih,
  { refl },
  { simp only [to_nat_succ, nat.bit_val],
    have h₁ : bv.not v 0 = !(v 0) := rfl,
    have h₂ : fin.tail (bv.not v) = bv.not (fin.tail v) := rfl,
    rw [h₁, h₂], clear h₁ h₂,
    rw [pow_succ, ← ih (fin.tail v)],
    cases v 0; simp only [cond, bnot]; ring }
end

end bitwise

section arithmetic
variable {n : ℕ}

/-- Addition. -/
protected def add (v₁ v₂ : fin n → bool) : fin n → bool :=
of_nat (to_nat v₁ + to_nat v₂)

/-- Negation. -/
protected def neg (v : fin n → bool) : fin n → bool :=
of_nat (2^n - to_nat v)

/-- Multiplication. -/
protected def mul (v₁ v₂ : fin n → bool) : fin n → bool :=
of_nat (to_nat v₁ * to_nat v₂)

instance : has_add (fin n → bool) :=
⟨bv.add⟩

instance : has_neg (fin n → bool) :=
⟨bv.neg⟩

instance : has_mul (fin n → bool) :=
⟨bv.mul⟩

lemma add_to_fin (v₁ v₂ : fin n → bool) :
  to_fin (v₁ + v₂) = to_fin v₁ + to_fin v₂ :=
begin
  dunfold to_fin has_add.add,
  simp [fin.add, bv.add, to_of_nat]
end

lemma neg_to_fin (v : fin n → bool) :
  to_fin (-v) = -(to_fin v) :=
begin
  have h : (2^n - to_nat v) % 2^n = (-(to_nat v : ℤ) % 2^n).to_nat,
  { rw [← int.add_mod_self_left, ← int.sub_eq_add_neg], norm_cast,
    rw ← int.coe_nat_sub (le_of_lt (to_nat_lt _)), norm_cast },
  dunfold to_fin has_neg.neg,
  simp [bv.neg, to_of_nat, int.nat_mod, h]
end

lemma mul_to_fin (v₁ v₂ : fin n → bool) :
  to_fin (v₁ * v₂) = to_fin v₁ * to_fin v₂ :=
begin
  dunfold to_fin has_mul.mul,
  simp [fin.mul, bv.mul, to_of_nat]
end

instance : comm_ring (fin n → bool) :=
{ add           := (+),
  zero          := 0,
  neg           := has_neg.neg,
  mul           := (*),
  one           := 1,
  add_assoc     := λ _ _ _, eq_of_to_fin_eq_to_fin $ by {
                     simp only [add_to_fin], abel },
  zero_add      := λ _, eq_of_to_fin_eq_to_fin $ by {
                     simp only [add_to_fin, zero_to_fin], abel },
  add_zero      := λ _, eq_of_to_fin_eq_to_fin $ by {
                     simp only [add_to_fin, zero_to_fin], abel },
  add_left_neg  := λ _, eq_of_to_fin_eq_to_fin $ by {
                     simp only [add_to_fin, neg_to_fin, zero_to_fin],
                     abel },
  add_comm      := λ _ _, eq_of_to_fin_eq_to_fin $ by {
                     simp only [add_to_fin], abel },
  mul_assoc     := λ _ _ _, eq_of_to_fin_eq_to_fin $ by {
                     simp only [mul_to_fin], ring },
  one_mul       := λ _, eq_of_to_fin_eq_to_fin $ by {
                     simp only [mul_to_fin, one_to_fin], ring },
  mul_one       := λ _, eq_of_to_fin_eq_to_fin $ by {
                     simp only [mul_to_fin, one_to_fin], ring },
  left_distrib  := λ _ _ _, eq_of_to_fin_eq_to_fin $ by {
                     simp only [add_to_fin, mul_to_fin], ring },
  right_distrib := λ _ _ _, eq_of_to_fin_eq_to_fin $ by {
                     simp only [add_to_fin, mul_to_fin], ring },
  mul_comm      := λ _ _, eq_of_to_fin_eq_to_fin $ by {
                     simp only [mul_to_fin], ring } }

/-! ### Extra instances to short-circuit type class resolution -/
instance : has_sub (fin n → bool)            := by apply_instance
instance : add_comm_monoid (fin n → bool)    := by apply_instance
instance : add_monoid (fin n → bool)         := by apply_instance
instance : monoid (fin n → bool)             := by apply_instance
instance : comm_monoid (fin n → bool)        := by apply_instance
instance : comm_semigroup (fin n → bool)     := by apply_instance
instance : semigroup (fin n → bool)          := by apply_instance
instance : add_comm_semigroup (fin n → bool) := by apply_instance
instance : add_semigroup (fin n → bool)      := by apply_instance
instance : comm_semiring (fin n → bool)      := by apply_instance
instance : semiring (fin n → bool)           := by apply_instance
instance : ring (fin n → bool)               := by apply_instance
instance : distrib (fin n → bool)            := by apply_instance

lemma add_to_nat (v₁ v₂ : fin n → bool) :
  to_nat (v₁ + v₂) = (to_nat v₁ + to_nat v₂) % 2^n :=
by apply to_of_nat

lemma neg_to_nat (v : fin n → bool) :
  to_nat (-v) = if to_nat v = 0 then 0 else 2^n - to_nat v :=
begin
  dunfold has_neg.neg bv.neg,
  simp only [to_of_nat],
  split_ifs with h,
  { simp [h] },
  { apply nat.mod_eq_of_lt,
    apply nat.sub_lt,
    { exact pow_pos dec_trivial n },
    { apply nat.pos_of_ne_zero h } }
end

theorem neg_eq_not_add_one : ∀ (v : fin n → bool),
  -v = bv.not v + 1 :=
begin
  induction n with n ih,
  { simp },
  { intro v,
    simp only [← to_nat_inj, has_neg.neg, bv.neg, to_of_nat, add_to_nat] at ih ⊢,
    simp only [one_to_nat],
    simp only [to_nat_succ, nat.bit_val, pow_succ],
    have h : ∀ i, bv.not v i = !v i,
    { simp [bv.not] },
    simp only [h], clear h,
    have h : fin.tail (bv.not v) = bv.not (fin.tail v),
    { simp [bv.not, fin.tail] },
    simp only [h], clear h,

    have h : 2 * 2^n - 2 * to_nat (fin.tail v) ≡
             2 * to_nat (bv.not (fin.tail v)) + 1 + 1 [MOD 2 * 2^n],
    { rw [← nat.mul_sub_left_distrib],
      rw [add_assoc, ← two_mul, ← left_distrib],
      apply nat.modeq.mul_left',
      cases n,
      { refl },
      { simp only [one_to_nat] at ih,
        apply ih } },

    cases v 0; simp only [cond, bool.bnot_false, bool.bnot_true, add_zero],
    { apply h },
    { apply nat.modeq.add_right_cancel (nat.modeq.refl 1),
      have hpos : 0 < 2 * 2^n - 2 * to_nat (fin.tail v),
      { apply nat.sub_pos_of_lt, mono; simp [to_nat_lt] },
      rw [← nat.sub_sub, nat.sub_add_cancel hpos],
      apply h } }
end

theorem sub_to_nat (v₁ v₂ : fin n → bool) :
  to_nat (v₁ - v₂) =
  if to_nat v₂ ≤ to_nat v₁ then
    to_nat v₁ - to_nat v₂
  else
    2^n + to_nat v₁ - to_nat v₂ :=
begin
  have h : v₁ - v₂ = v₁ + (-v₂) := rfl,
  rw h, clear h,
  simp only [add_to_nat, neg_to_nat],
  have hlt₁ := to_nat_lt v₁,
  have hlt₂ := to_nat_lt v₂,
  split_ifs with h₁ h₂,
  { simp only [h₁, add_zero, nat.sub_zero],
    exact nat.mod_eq_of_lt hlt₁ },
  { simp only [h₁] at h₂,
    simpa using h₂ },
  { have h : to_nat v₁ + (2^n - to_nat v₂) = 2^n + (to_nat v₁ - to_nat v₂), by omega,
    rw h, clear h,
    rw [nat.add_mod_left, nat.mod_eq_of_lt],
    omega },
  { have h : to_nat v₁ + (2^n - to_nat v₂) = 2^n + to_nat v₁ - to_nat v₂, by omega,
    rw h, clear h,
    apply nat.mod_eq_of_lt,
    omega }
end

lemma mul_to_nat (v₁ v₂ : fin n → bool) :
  to_nat (v₁ * v₂) = (to_nat v₁ * to_nat v₂) % 2^n :=
by apply to_of_nat

/-- Unsigned division. -/
protected def udiv (v₁ v₂ : fin n → bool) : fin n → bool :=
if to_nat v₂ = 0 then ⊤ else of_nat (to_nat v₁ / to_nat v₂)

instance : has_div (fin n → bool) :=
⟨bv.udiv⟩

/-- Unsigned remainder. -/
protected def urem (v₁ v₂ : fin n → bool) : fin n → bool :=
of_nat (to_nat v₁ % to_nat v₂)

instance : has_mod (fin n → bool) :=
⟨bv.urem⟩

theorem udiv_to_nat (v₁ v₂ : fin n → bool) :
  to_nat (v₁ / v₂) = if to_nat v₂ = 0 then 2^n - 1 else to_nat v₁ / to_nat v₂ :=
begin
  conv_lhs { simp only [has_div.div] },
  simp only [bv.udiv],
  split_ifs,
  { simp [top_to_nat] },
  { simp only [to_of_nat],
    apply nat.mod_eq_of_lt,
    exact lt_of_le_of_lt (nat.div_le_self _ _) (to_nat_lt _) }
end

theorem urem_to_nat (v₁ v₂ : fin n → bool) :
  to_nat (v₁ % v₂) = to_nat v₁ % to_nat v₂ :=
begin
  conv_lhs { simp only [has_mod.mod] },
  simp only [bv.urem],
  simp only [to_of_nat],
  cases nat.eq_zero_or_pos (to_nat v₂) with h h,
  { simp only [h, nat.mod_zero],
    apply nat.mod_eq_of_lt (to_nat_lt _) },
  { apply nat.mod_eq_of_lt,
    apply lt_trans (nat.mod_lt _ h) (to_nat_lt v₂) }
end

end arithmetic

/-! ### Shift operators

These shift operators use `n₁` and `n₂` as the bitwidths of the value and of the shifting amount,
respectively, allowing for `n₁ = n₂` or `n₁ = 2^n₂`.
-/
section shift
variables {n₁ n₂ : ℕ}

/-- Left shift. -/
protected def shl (v₁ : fin n₁ → bool) (v₂ : fin n₂ → bool) : fin n₁ → bool :=
of_nat (to_nat v₁ * 2^(to_nat v₂))

/-- Logical right shift. -/
protected def lshr (v₁ : fin n₁ → bool) (v₂ : fin n₂ → bool) : fin n₁ → bool :=
of_nat (to_nat v₁ / 2^(to_nat v₂))

/-- Arithmetic shift right. -/
protected def ashr (v₁ : fin n₁ → bool) (v₂ : fin n₂ → bool) : (fin n₁ → bool) :=
cond (bv.msb v₁) (bv.not (bv.lshr (bv.not v₁) v₂)) (bv.lshr v₁ v₂)

theorem shl_to_nat (v₁ : fin n₁ → bool) (v₂ : fin n₂ → bool) :
  to_nat (bv.shl v₁ v₂) = to_nat v₁ * 2^to_nat v₂ % 2^n₁ :=
by simp only [bv.shl, to_of_nat]

theorem lshr_to_nat (v₁ : fin n₁ → bool) (v₂ : fin n₂ → bool) :
  to_nat (bv.lshr v₁ v₂) = to_nat v₁ / 2^to_nat v₂ :=
begin
  simp only [bv.lshr, to_of_nat],
  apply nat.mod_eq_of_lt,
  exact lt_of_le_of_lt (nat.div_le_self _ _) (to_nat_lt _)
end

end shift

/-! ### Relational operators

SMT-LIB defines `bvult` as the core operator, while `preorder` uses `≤` as the core operator.
We explicitly define both `ult` and `ule` with `lt_iff_le_not_le` as the consistency check.

This aims to override `≤` provided by `pi.partial_order`.
-/
section relational
variable {n : ℕ}

/-- Unsigned less than. -/
protected def ult (v₁ v₂ : fin n → bool) : Prop :=
to_nat v₁ < to_nat v₂

/-- Unsigned less than or equal. -/
protected def ule (v₁ v₂ : fin n → bool) : Prop :=
to_nat v₁ ≤ to_nat v₂

instance : has_lt (fin n → bool) :=
⟨bv.ult⟩

instance : has_le (fin n → bool) :=
⟨bv.ule⟩

instance preorder : preorder (fin n → bool) :=
{ le               := (≤),
  lt               := (<),
  le_refl          := λ _, @le_refl ℕ _ _,
  le_trans         := λ _ _ _, @le_trans ℕ _ _ _ _,
  lt_iff_le_not_le := λ _ _, @lt_iff_le_not_le ℕ _ _ _ }

instance partial_order : partial_order (fin n → bool) :=
{ le_antisymm      := λ _ _ h₁ h₂, eq_of_to_nat_eq_to_nat (@le_antisymm ℕ _ _ _ h₁ h₂),
  .. bv.preorder }

instance linear_order : linear_order (fin n → bool) :=
{ le_total         := λ _ _, @le_total ℕ _ _ _,
  decidable_le     := λ _ _, (infer_instance : decidable (to_nat _ ≤ to_nat _)),
  .. bv.partial_order }

/-- Signed less than. -/
protected def slt (v₁ v₂ : fin n → bool) : Prop :=
(msb v₁ = tt ∧ msb v₂ = ff) ∨ (msb v₁ = msb v₂ ∧ v₁ < v₂)

/-- Signed less than or equal. -/
protected def sle (v₁ v₂ : fin n → bool) : Prop :=
(msb v₁ = tt ∧ msb v₂ = ff) ∨ (msb v₁ = msb v₂ ∧ v₁ ≤ v₂)

protected theorem sle_iff_eq_or_slt {n : ℕ} {v₁ v₂ : fin n → bool} :
  bv.sle v₁ v₂ ↔ v₁ = v₂ ∨ bv.slt v₁ v₂ :=
begin
  simp only [bv.sle, bv.slt],
  rw [le_iff_eq_or_lt],
  tauto
end

protected theorem not_slt {n : ℕ} {v₁ v₂ : fin n → bool} :
  ¬ bv.slt v₁ v₂ ↔ bv.sle v₂ v₁ :=
begin
  simp only [bv.sle, bv.slt],
  cases msb v₁; cases msb v₂; simp
end

instance decidable_slt : @decidable_rel (fin n → bool) bv.slt :=
λ _ _, by { dsimp [bv.slt], apply_instance }

instance decidable_sle : @decidable_rel (fin n → bool) bv.sle :=
λ _ _, by { dsimp [bv.sle], apply_instance }

/-- Signed greater than. -/
@[reducible]
protected def sgt (v₁ v₂ : fin n → bool) : Prop :=
bv.slt v₂ v₁

/-- Signed greater than or equal. -/
@[reducible]
protected def sge (v₁ v₂ : fin n → bool) : Prop :=
bv.sle v₂ v₁

end relational

section misc

/-- Concatenation of two bitvectors. -/
def concat {n₁ n₂ : ℕ} (v₁ : fin n₁ → bool) (v₂ : fin n₂ → bool) : fin (n₁ + n₂) → bool :=
λ ⟨x, h₁⟩, if h₂ : x < n₂ then v₂ ⟨x, h₂⟩ else v₁ ⟨x - n₂, by omega⟩

theorem list_of_fn_concat {n₁ n₂ : ℕ} {v₁ : fin n₁ → bool} {v₂ : fin n₂ → bool} :
  list.of_fn (concat v₁ v₂) = (list.of_fn v₂) ++ (list.of_fn v₁) :=
begin
  apply list.ext,
  intros i,
  simp only [list.nth_of_fn, list.of_fn_nth_val, list.nth_append_eq_ite, list.length_of_fn, concat],
  split_ifs with h₁ h₂ h₃,
  { refl },
  { refl },
  { apply h₃, omega },
  { apply h₁, omega },
  { apply h, omega },
  { refl }
end

/-- Extraction of bits i down to j of a bitvector. -/
def extract {n : ℕ} (i j : ℕ) (hi : i < n) (hj : j ≤ i) (v : fin n → bool) : fin (i - j + 1) → bool :=
λ ⟨x, h⟩, v ⟨j + x, by omega⟩

theorem extract_msb {n : ℕ} {v : fin (n + 1) → bool} {i : fin _} {h₁ : _} {h₂ : _} :
  extract n n h₁ h₂ v i = msb v :=
begin
  rcases i with ⟨i, h⟩,
  simp only [extract, msb],
  congr,
  have : i = 0, by omega, subst this,
  simp only [add_zero]
end

theorem list_of_fn_extract {upper lower n : ℕ} {h₁ : _} {h₂ : _} {v : fin n → bool} :
  list.of_fn (bv.extract upper lower h₁ h₂ v) = ((list.of_fn v).drop lower).take (upper - lower + 1) :=
begin
  apply list.ext,
  intros i,
  rw [list.nth_of_fn],
  by_cases b : i < upper - lower + 1,
  { rw [list.nth_take b, list.of_fn_nth_val, dif_pos b, list.nth_drop, list.nth_of_fn, list.of_fn_nth_val, dif_pos],
    congr },
  { rw [list.of_fn_nth_val, dif_neg b],
    symmetry,
    rw [list.nth_eq_none_iff, list.length_take, list.length_drop, list.length_of_fn],
    rw [not_lt] at b,
    rw [min_le_iff],
    left,
    from b }
end

/-- Conditional operator. -/
def ite {n : ℕ} (v₁ : fin 1 → bool) (v₂ v₃ : fin n → bool) : fin n → bool :=
cond (v₁ 0) v₂ v₃

end misc

end bv
