/-
Copyright (c) 2021 The UNSAT Group. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luke Nelson, Xi Wang
-/
import .default
import .parser
import misc.semidecision

namespace sat
namespace proof

/-- Obtain a LRAT proof via a script, which invokes a SAT solver and drat-trim. -/
def run_sat (s : string) : io string := do
child ← io.proc.spawn {
  cmd    := "bin/sat.py",
  stdin  := io.process.stdio.piped,
  stdout := io.process.stdio.piped },
io.fs.put_str child.stdin s,
io.fs.close child.stdin,
buf ← io.fs.read_to_end child.stdout,
io.fs.close child.stdout,
exitv ← io.proc.wait child,
when (exitv ≠ 0) $ io.fail "error in `bin/sat.py'",
return buf.to_string

/-- Obtain an LRAT proof from the SAT solver. -/
meta def sat_oracle : semidecision.oracle sat.cnf.default.formula sat.proof.default.proof := λ f, do
proof ← tactic.unsafe_run_io $ run_sat $ sat.cnf.formula.dimacs f,
-- trace proof,
match parser.run sat.parser.lrat proof.to_char_buffer with
| sum.inr as  := pure as
| sum.inl err := tactic.fail err
end

end proof
end sat
