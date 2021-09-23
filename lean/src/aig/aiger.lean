/-
Copyright (c) 2021 The UNSAT Group. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luke Nelson, Xi Wang
-/
import .basic
import sat.parser

/-!
# AIGER

This file provides printing and parsing support for the AIGER format.

## Implementation notes

AIGER has two versions, ASCII and binary. The ASCII version imposes fewer constraints, while the
binary version is strict (e.g., literals are ordered, with no unused ones). Therefore, printing
uses the ASCII version and parsing uses the binary format.

## References

* <http://fmv.jku.at/aiger/>
-/

namespace aig

namespace ref
variables {α σ : Type*} [unordered_map α (node α) σ] [has_coe_t α ℕ]

private def aiger_input : α → node α → option ℕ
| id (node.var _) := some $ bit0 (id : ℕ)
| id _            := none

private def aiger_output : ref α → ℕ
| top        := 1
| bot        := 0
| (root a b) := nat.bit b a

private def aiger_and : α → node α → option (list ℕ)
| id (node.and a₁ b₁ a₂ b₂) := [bit0 (id : ℕ), nat.bit b₁ a₁, nat.bit b₂ a₂]
| _  _                      := none

/-- Print a multi-rooted AIG in the AIGER format. -/
def aiger_all (g : σ) (rs : list (ref α)) : string :=
string.join $ list.map (λ s, string.push s '\n') $
  let ns := unordered_map.to_list g,
      m  := (ns.map $ λ (x : Σ _ : α, _), (x.1 : ℕ)).maximum.get_or_else 0,
      is := (ns.filter_map $ λ (x : Σ _, node α), aiger_input x.1 x.2).map repr,
      os := (rs.map aiger_output).map repr,
      as := (ns.filter_map $ λ (x : Σ _, node α), aiger_and x.1 x.2).map (λ l, " ".intercalate (l.map repr)) in
  ("aag " ++ repr m ++ " " ++ " ".intercalate ([is.length, 0, os.length, as.length].map repr)) ::
  (is ++ os ++ as)

/-- Print an AIG in the DOT format. -/
def aiger (g : σ) (r : ref α) : string :=
aiger_all g [r]

end ref
end aig

section monad
universe u

/-- Repeat a monadic action `n` times and collect the results as a list. -/
def mreplicate {m : Type u → Type*} [monad m] {α : Type u} : ℕ → m α → m (list α)
| 0       _ := pure []
| (n + 1) p := list.cons <$> p <*> mreplicate n p

/-- Repeat a monadic action `n` times and ignore the results. -/
def mreplicate' {m : Type → Type*} [monad m] {α : Type} : ℕ → m α → m unit
| 0       _ := pure ()
| (n + 1) p := p >> mreplicate' n p

end monad

namespace parser

/-- Match an integer encoded using unsigned LEB128.

Each value is encoded as 7-bit chunks, starting from least significant, with the MSB set on each
byte except for the last.
-/
def uleb128 : parser num := decorate_error "<uleb128>" $ do
cs ← many $ sat (λ c, 0x80 ≤ c.to_nat ∧ c.to_nat ≤ 0xff),
last ← sat (λ c, c.to_nat ≤ 0x7f),
pure $ cs.foldr
  (λ (c : char) (sum : num), sum.shiftl 7 + (c.to_nat : num).land 0x7f)
  (last.to_nat : num)

end parser

namespace aig
namespace parser
open parser

namespace aiger

/-- Match a header. -/
def header : parser (ℕ × ℕ × ℕ) := do
str "aig",
m ← ch ' ' >> nat,
i ← ch ' ' >> nat,
-- No support for latches.
decorate_error "<L = 0>" $
  ch ' ' >> ch '0',
o ← ch ' ' >> nat,
a ← ch ' ' >> nat,
guard $ m = i + a,
-- No support for extensions.
decorate_error "<B, C, J, F = 0>" $
  many (ch ' ' >> ch '0'),
newline,
pure (i, o, a)

/-- Match a literal encoded as a sign bit and variable value. -/
def literal : parser (pos_num × bool) :=
decorate_error "<literal>" $ do
n ← positive,
pure $ (pos_num.of_znum (num.pos n).div2, n.test_bit 0)

/-- Match a symbol. -/
def symbol : parser unit :=
decorate_error "<symbol>" $ do
one_of ['i', 'l', 'o'],
many' (sat (λ c, c ≠ '\n')) >> newline

/-- Match a comment section. -/
def comment : parser unit :=
decorate_error "<comment>" $ do
ch 'c' >> newline >> many' any_char

/-- Construct an AIG from parsed AIGER data. -/
def mk (ni : ℕ) (ands : list (num × num)) :
  state (pos_num × trie (node pos_num)) unit := do
-- Create input variables using dummy `tt` (the value doesn't matter).
mreplicate' ni (modify $ λ ⟨nextid, g⟩, (counter.next nextid, node.insert_var g nextid $ erased.mk tt)),
-- Create AND gates.
ands.mmap' $ λ ⟨d₁, d₂⟩, (modify $ λ ⟨nextid, g⟩,
  let o := num.pos (nextid.shiftl 1), i₁ := o - d₁, i₂ := i₁ - d₂,
      n₁ := pos_num.of_znum i₁.div2, b₁ := i₁.test_bit 0,
      n₂ := pos_num.of_znum i₂.div2, b₂ := i₂.test_bit 0 in
  (counter.next nextid, node.insert_and g nextid n₁ b₁ n₂ b₂))

end aiger

/-- Parse an AIG in the AIGER binary format. -/
def aiger : parser (trie (node pos_num) × list (ref pos_num)) := do
-- Parse the header.
(ni, no, na) ← aiger.header,
-- Parse output nodes.
os ← mreplicate no (aiger.literal <* newline),
-- Each AND gate is stored as a pair of delta values: (lhs - rhs₁, rhs₁ - rhs₂).
ands ← mreplicate na (prod.mk <$> uleb128 <*> uleb128),
-- Skip the symbol table and comment section.
many' aiger.symbol,
aiger.comment <|> eof,
-- Construct an AIG.
pure ((((aiger.mk ni ands)).run (1, ∅)).2.2, os.map (λ ⟨a, b⟩, ref.root a b))

end parser
end aig
