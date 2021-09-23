/-
Copyright (c) 2021 The UNSAT Group. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luke Nelson, Xi Wang
-/
import data.vector
import data.bitvec.basic
open nat

/-!
# WF performance issue example

An example demonstrating the issue with well-founded recursion in the kernel.
-/

namespace example1

-- An example vector [ff, ff]
def myvec : vector bool 2 := vector.cons ff (vector.cons ff vector.nil)

/-
Define a function that returns ff for any vector via recursion.
The equation compiler turns this into well-founded recursion over the vector.
-/
def my_wf_function : ∀ {n : ℕ}, vector bool n → bool
| 0       _ := ff
| (n + 1) v := my_wf_function (vector.tail v)

-- #print my_wf_function._main._pack

-- VM evaluation succeeds.
-- #eval my_wf_function myvec

-- Kernel reduction dies
-- #reduce my_wf_function myvec

-- refl proof dies
-- example : my_wf_function myvec = ff := by refl

/-
Define a new version of the function which uses structural induction over n.
-/
def my_structural_function : ∀ {n : ℕ}, vector bool n → bool
| 0       v := ff
| (n + 1) v := @my_structural_function n (vector.tail v)

-- VM evaluation still succeeds
-- #eval my_structural_function myvec

-- Kernel reduction succeeds
-- #reduce my_structural_function myvec

-- refl proof succeeds
example : my_structural_function myvec = ff := by refl

end example1

-- #reduce @well_founded.fix _ _ _ (empty_wf) (λ _ _, ff) tt
