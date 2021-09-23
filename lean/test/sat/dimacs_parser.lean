/-
Copyright (c) 2021 The UNSAT Group. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luke Nelson, Xi Wang
-/
import sat.parser

def main : io unit := do
buf ← io.stdin >>= io.fs.read_to_end,
match parser.run sat.parser.dimacs buf with
| sum.inr f   := io.print $ sat.cnf.formula.dimacs f
| sum.inl err := io.fail err
end
