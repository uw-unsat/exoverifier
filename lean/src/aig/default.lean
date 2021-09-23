/-
Copyright (c) 2021 The UNSAT Group. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luke Nelson, Xi Wang
-/
import .basic
import .factory
import .to_cnf
import sat.default

namespace aig
namespace default

/-- Default node type. -/
abbreviation node : Type := aig.node pos_num

/-- Default reference type. -/
abbreviation ref : Type := aig.ref pos_num

/-- Default reference type with concrete value. -/
abbreviation bref : Type := aig.bref pos_num

/-- Default factory type. -/
abbreviation factory : Type := aig.factory pos_num (trie node)

open sat.cnf

abbreviation decide_via_to_cnf : factory.decision_procedure bool bref factory sat.proof.default.proof :=
aig.decide_via_to_cnf

abbreviation decide_via_trivial {ω : Type*} : factory.decision_procedure bool bref factory ω :=
aig.decide_via_trivial

end default
end aig
