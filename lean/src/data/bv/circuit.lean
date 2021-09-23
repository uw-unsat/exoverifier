/-
Copyright (c) 2021 The UNSAT Group. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luke Nelson, Xi Wang
-/
import .basic
import .vector
import sat.bool
import smt.bitblast.basic
import smt.bitblast.default
import smt.factory

/-!
# Circuit implementations of bitvector operations.
-/

namespace bv
namespace circuit
open smt.bitblast

def add {n : ℕ} (x y : lsbvector n) : lsbvector n :=
((mk_add x y).run punit.star).1.1

theorem nth_add {n : ℕ} {x y : lsbvector n} :
  (add x y).nth = x.nth + y.nth :=
begin
  simp only [add],
  rcases mk : (mk_add x y).run punit.star with ⟨⟨_, _⟩, ⟨⟩⟩,
  obtain ⟨h, -⟩ := eval_mk_add mk (by rw [eval.iff_trivial]) (by rw [eval.iff_trivial]),
  rw [eval.iff_trivial] at h,
  rw [h]
end

def mul {n : ℕ} (x y : lsbvector n) : lsbvector n :=
((mk_mul x y).run punit.star).1

theorem nth_mul {n : ℕ} {x y : lsbvector n} :
  (mul x y).nth = x.nth * y.nth :=
begin
  simp only [mul],
  rcases mk : (mk_mul x y).run punit.star with ⟨⟨_, _⟩, ⟨⟩⟩,
  obtain h := eval_mk_mul mk (by rw [eval.iff_trivial]) (by rw [eval.iff_trivial]),
  rw [eval.iff_trivial] at h,
  rw [h]
end

def udiv {n : ℕ} (x y : lsbvector n) : lsbvector n :=
((mk_udiv x y).run punit.star).1

theorem nth_udiv {n : ℕ} {x y : lsbvector n} :
  (udiv x y).nth = x.nth / y.nth :=
begin
  simp only [udiv],
  rcases mk : (mk_udiv x y).run punit.star with ⟨⟨_, _⟩, ⟨⟩⟩,
  obtain h := eval_mk_udiv mk (by rw [eval.iff_trivial]) (by rw [eval.iff_trivial]),
  rw [eval.iff_trivial] at h,
  rw [h]
end

def urem {n : ℕ} (x y : lsbvector n) : lsbvector n :=
((mk_urem x y).run punit.star).1

theorem nth_urem {n : ℕ} {x y : lsbvector n} :
  (urem x y).nth = x.nth % y.nth :=
begin
  simp only [urem],
  rcases mk : (mk_urem x y).run punit.star with ⟨⟨_, _⟩, ⟨⟩⟩,
  obtain h := eval_mk_urem mk (by rw [eval.iff_trivial]) (by rw [eval.iff_trivial]),
  rw [eval.iff_trivial] at h,
  rw [h]
end

def and {n : ℕ} (x y : lsbvector n) : lsbvector n :=
vector.map₂ band x y

theorem nth_and {n : ℕ} {x y : lsbvector n} :
  (and x y).nth = bv.and x.nth y.nth :=
begin
  ext i,
  simp only [and, vector.nth_map₂],
  refl
end

def or {n : ℕ} (x y : lsbvector n) : lsbvector n :=
vector.map₂ bor x y

theorem nth_or {n : ℕ} {x y : lsbvector n} :
  (or x y).nth = bv.or x.nth y.nth :=
begin
  ext i,
  simp only [or, vector.nth_map₂],
  refl
end

def xor {n : ℕ} (x y : lsbvector n) : lsbvector n :=
vector.map₂ bxor x y

theorem nth_xor {n : ℕ} {x y : lsbvector n} :
  (xor x y).nth = bv.xor x.nth y.nth :=
begin
  ext i,
  simp only [xor, vector.nth_map₂],
  refl
end

def not {n : ℕ} (x : lsbvector n) : lsbvector n :=
vector.map bnot x

theorem nth_not {n : ℕ} {x : lsbvector n} :
  (not x).nth = bv.not x.nth :=
begin
  ext i,
  simp only [not, vector.nth_map],
  refl
end

def ult {n : ℕ} (x y : lsbvector n) : bool :=
((mk_ult x y).run punit.star).1.head

theorem ult_eq_ult_unwrap.nth {n : ℕ} {x y : lsbvector n} :
  ult x y = to_bool (x.nth < y.nth) :=
begin
  simp only [ult],
  rcases mk : (mk_ult x y).run punit.star with ⟨⟨_, _⟩, ⟨⟩⟩,
  have h := eval_mk_ult mk (by rw [eval.iff_trivial]) (by rw [eval.iff_trivial]),
  simp only [eval.iff_trivial] at h,
  simp only [← vector.nth_zero, ← h]
end

end circuit
end bv
