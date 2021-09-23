/-
Copyright (c) 2021 The UNSAT Group. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luke Nelson, Xi Wang
-/
import ..cfg
import .basic
import aig.basic
import aig.default
import aig.to_cnf
import smt.bitblast.basic
import smt.bitblast.default

namespace bpf
namespace cfg
namespace se
namespace default

abbreviation vcgen : cfg.trie_program → ℕ → erased (vector i64 bpf.nregs) → state aig.default.factory (Σ n, vector aig.default.bref n) :=
vcgen

end default
end se
end cfg
end bpf
