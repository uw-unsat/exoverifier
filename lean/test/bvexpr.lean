/-
Copyright (c) 2021 The UNSAT Group. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luke Nelson, Xi Wang
-/
-- import bv.basic
-- import bv.expr

-- section example_
-- open bv

-- -- def x : Expr ℕ (Ty.Bv 8) := Expr.Var 0
-- -- def y : Expr ℕ (Ty.Bv 8) := Expr.Var 1
-- -- def exp : Expr ℕ Ty.Bool := Expr.BvEq x y

-- -- def cbc' := state_t.run (compile _ exp) sat.cbc.factory.init
-- -- def cbc : (sat.cbc ℕ × sat.cbc.factory ℕ) := cbc'

-- -- def form : sat.cnf.formula ℕ := function.uncurry sat.cbc.compile cbc

-- -- #eval form

-- end example_
