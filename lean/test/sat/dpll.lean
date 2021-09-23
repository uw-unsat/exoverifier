/-
Copyright (c) 2021 The UNSAT Group. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luke Nelson, Xi Wang
-/
import sat.dpll
import sat.parser

/-- Parse a CNF string. -/
meta def get_cnf (s : string) : tactic unit :=
match parser.run sat.parser.dimacs s.to_char_buffer with
| sum.inr f   := tactic.exact `(f)
| sum.inl err := tactic.fail err
end

/-- Test CNF input. -/
def test : string :=
"p cnf 4 8
 1  2 -3 0
-1 -2  3 0
 2  3 -4 0
-2 -3  4 0
-1 -3 -4 0
 1  3  4 0
-1  2  4 0
 1 -2 -4 0"

example : unsatisfiable (by get_cnf test) :=
semidec_trivial (sat.decide_unsat_via_dpll _ unit.star)
