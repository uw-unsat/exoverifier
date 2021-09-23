/-
Copyright (c) 2021 The UNSAT Group. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luke Nelson, Xi Wang
-/
import aig.aiger
import aig.to_cnf
import aig.default

def main : io unit := do
-- Make stdin in binary mode for the AIGER binary format. Note that Lean's stdin is in text mode,
-- reading from which may drop non-text characters and break parsing.
buf ← io.mk_file_handle "/dev/stdin" io.mode.read tt >>= io.fs.read_to_end,
match parser.run aig.parser.aiger buf with
| sum.inr ⟨g, [r]⟩ :=
  match (aig.ref.to_cnf g r : option sat.cnf.default.formula) with
  | (some f) := io.print $ sat.cnf.formula.dimacs f
  | none     := io.fail "error in `to_cnf`"
  end
| sum.inr _        := io.fail "must have only one output"
| sum.inl err      := io.fail err
end
