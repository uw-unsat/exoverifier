/-
Copyright (c) 2021 The UNSAT Group. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luke Nelson, Xi Wang
-/
import .basic
import ..data.counter
import ..data.unordered_map.basic

namespace aig
namespace ref
variables {α σ : Type*} [has_repr α] [counter α] [unordered_map α (aig.node α) σ]

open unordered_map

private def dot_output : ref α → list string
| top        := ["_ [label=\"⊤\"]"]
| bot        := ["_ [label=\"⊥\"]"]
| (root a b) := ["o" ++ repr a ++ " [shape=none,label=\"\"];",
                 "o" ++ repr a ++ " -> x" ++ repr a ++ cond b ";" " [arrowhead=dot];"]

private def dot_gate : α → node α → list string
| id (node.var _)           := []
| id (node.and a₁ b₁ a₂ b₂) := let f := λ (n : α) b,
  "x" ++ repr id ++ " -> x" ++ repr n ++ cond b ";" " [arrowhead=dot];" in
  [f a₁ b₁, f a₂ b₂]

private def uncurry_sig {T : Type*} (f : α → node α → T) : (Σ (_ : α), node α) → T :=
  λ x, f x.1 x.2

/-- Print a multi-rooted AIG in the DOT format. -/
def dot_all (g : σ) (rs : list (ref α)) : string :=
"\n".intercalate $ ["digraph {"] ++ rs.bind dot_output ++ (to_list g).bind (uncurry_sig dot_gate) ++ ["}"]

/-- Print an AIG in the DOT format. -/
def dot (g : σ) (r : ref α) : string :=
dot_all g [r]

end ref
end aig
