/-
Copyright (c) 2021 The UNSAT Group. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luke Nelson, Xi Wang
-/
import aig.aiger
import aig.factory
import tactic.io

/-!
# AIG examples

This file shows basic examples of AIGs.

## References

* Armin Biere. *The AIGER And-Inverter Graph (AIG) Format Version 20071012*.
  <http://fmv.jku.at/papers/Biere-FMV-TR-07-1.pdf>
-/

/-- Read an example AIG file. -/
meta def file (name : string) : tactic unit :=
`[tactic.io.from_file_as_string $ "test/aig/examples/" ++ name]

/-- Run a state monad that produces an AIG in the AIGER format. -/
def eval (s : state (aig.factory pos_num (trie (aig.node pos_num))) (aig.bref pos_num)) : string :=
let ⟨r, g⟩ := s.run aig.factory.init in
r.1.aiger g.nodes

section
variables (i₀ i₁ : erased bool)

open sat.and_factory
open sat.const_factory
open sat.implies_factory
open sat.not_factory
open sat.or_factory
open sat.var_factory

example : eval (mk_true <$> get) = by file "true.aag" :=
rfl

example : eval (mk_false <$> get) = by file "false.aag" :=
rfl

example : eval (mk_var i₀) = by file "buffer.aag" :=
rfl

example : eval (mk_var i₀ >>= mk_not) = by file "inverter.aag" :=
rfl

example : eval (mjoin $ mk_and <$> mk_var i₀ <*> mk_var i₁) = by file "and.aag" :=
rfl

example : eval (mjoin $ mk_or <$> mk_var i₀ <*> mk_var i₁) = by file "or.aag" :=
rfl

example : eval (mjoin $ mk_implies <$> mk_var i₀ <*> mk_var i₁) = by file "implies.aag" :=
rfl

example : eval (mjoin (mk_and <$> mk_var i₀ <*> mk_var i₁) >>= mk_not) = by file "nand.aag" :=
rfl

example : eval (mjoin (mk_or <$> mk_var i₀ <*> mk_var i₁) >>= mk_not) = by file "nor.aag" :=
rfl

end
