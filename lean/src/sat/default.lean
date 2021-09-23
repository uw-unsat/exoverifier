/-
Copyright (c) 2021 The UNSAT Group. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luke Nelson, Xi Wang
-/
import .cnf
import .proof

namespace sat
namespace cnf
namespace default

/-- Default clause type. -/
abbreviation clause : Type := trie bool

/-- Default formula type. -/
abbreviation formula : Type := trie clause

instance : cnf.clause pos_num clause :=
{ }

instance : cnf.formula pos_num clause formula :=
{ }

end default
end cnf

namespace proof
namespace default
open sat.cnf.default

/-- Default proof action type. -/
abbreviation action : Type := sat.proof.action pos_num clause pos_num formula

/-- Default proof type. -/
abbreviation proof : Type := sat.proof.proof pos_num clause pos_num formula

end default
end proof
end sat
