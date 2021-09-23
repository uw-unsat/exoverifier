/-
Copyright (c) 2021 The UNSAT Group. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luke Nelson, Xi Wang
-/
import sat.tactic

def main : io unit := do
buf ← io.stdin >>= io.fs.read_to_end,
cnf ← match parser.run sat.parser.dimacs buf with
| sum.inr cnf := pure cnf
| sum.inl err := io.fail err
end,
proof ← sat.proof.run_sat $ sat.cnf.formula.dimacs cnf,
as ← match parser.run_string sat.parser.lrat proof with
| sum.inr as  := pure as
| sum.inl err := io.fail err
end,
match sat.proof.rup_check cnf as with
| sat.proof.result.ok := pure ()
| err                 := io.fail $ repr err
end
