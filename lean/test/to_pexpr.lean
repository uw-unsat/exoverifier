/-
Copyright (c) 2021 The UNSAT Group. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luke Nelson, Xi Wang
-/
import data.bitvec.basic
import misc.fin_enum
import misc.list
import misc.option
import misc.vector

/- Tests for our method of reflecting proofs/programs from meta lean to regular lean. -/

namespace test_to_pexpr
open tactic

/- Test for vectors of bools. -/
def v₁ : vector bool 8 := 42
meta def v₁_expr : pexpr := to_pexpr v₁
def v₁' : vector bool 8 := by to_expr v₁_expr >>= exact
example : v₁ = v₁' := by refl

/- Test for functions over a finite, enumerable type (e.g., reg, fin n). -/
def f₁ : fin 11 → bool := λ x, if x > 8 then tt else ff
meta def f₁_expr : pexpr := ``(%%(to_pexpr f₁) : fin 11 → bool)
def f₁' : fin 11 → bool := by to_expr f₁_expr >>= exact
example : f₁ = f₁' := by dec_trivial

end test_to_pexpr
