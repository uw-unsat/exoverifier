/-
Copyright (c) 2021 The UNSAT Group. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luke Nelson, Xi Wang
-/
import .proof
import .default
import data.unordered_map.trie
import data.buffer.parser

namespace parser

/-- Match a whitespace character. -/
def space : parser char :=
one_of [' ', '\t', '\n', char.of_nat 0x0b, char.of_nat 0x0d]

/-- Match zero or more whitespace characters. -/
def spaces : parser unit :=
many' space

/-- Match a newline. -/
def newline : parser unit :=
ch '\n' >> eps

/-- Match a positive number. -/
def positive : parser pos_num := decorate_error "<positive>" $ do
c ← sat (λ c, '1' ≤ c ∧ c ≤ '9'),
digits ← many digit,
pure $ digits.foldl
  (λ sum digit, digit.repeat (λ _, pos_num.succ) (sum * 10))
  (pos_num.of_nat (c.to_nat - '0'.to_nat))

end parser

namespace sat
namespace parser

open _root_.parser

/-- Match a CNF literal. -/
def literal : parser (cnf.literal pos_num) :=
cnf.literal.mk_pos <$> positive <|>
cnf.literal.mk_neg <$> (ch '-' >> positive)

namespace dimacs

/-- Match a CNF clause. -/
def clause : parser (trie bool) := do
cnf.clause.of_list <$> (spaces >> many (literal <* spaces) <* ch '0')

/-- Match a comment line. -/
def comment : parser unit := do
sat (λ c, c = 'c'),
many' (sat (λ c, c ≠ '\n'))

/-- Match a problem line and return the number of clauses. -/
def problem : parser ℕ := do
sat (λ c, c = 'p'),
spaces >> str "cnf" >> spaces >> nat >> spaces >> nat

end dimacs

/-- Match a CNF formula in the DIMACS format. -/
def dimacs : parser (trie (trie bool)) := do
n ← many (dimacs.comment <* spaces) >> (dimacs.problem <* spaces),
cs ← many (dimacs.clause <* spaces),
decorate_error (repr n ++ " clause" ++ (cond (n = 1) "" "s") ++ ", found " ++ repr cs.length) $
guard $ cs.length = n,
pure $ cnf.formula.of_list cs

namespace lrat

/-- Match a RAT hint, a negated clause ID followed by a list of clause IDs. -/
def drat_hint : parser (pos_num × list pos_num) := do
sat (λ c, c = '-'),
prod.mk <$> (positive <* spaces) <*> many (positive <* spaces)

/-- Match a clause addition. -/
def action_add (k : pos_num) : parser proof.default.action := do
ls ← many (literal <* spaces) <* ch '0' <* spaces,
ks ← many (positive <* spaces),
match ls with
| []       := failure
| hd :: tl := do
  hints ← many1 drat_hint <* ch '0',
  pure $ proof.action.rat k hd (cnf.clause.of_list (hd :: tl)) ks hints
end <|> do
hints ← many (positive <* spaces) <* ch '0',
pure $ proof.action.rup k (cnf.clause.of_list ls) (ks ++ hints)

/-- Match a clause deletion. -/
def action_del (k : pos_num) : parser proof.default.action := do
sat (λ c, c = 'd'),
hints ← spaces >> many (positive <* spaces) <* ch '0',
pure $ proof.action.del k (hints.foldl (λ f k, f.kinsert k trie.nil) trie.nil)

/-- Match a proof action. -/
def action : parser proof.default.action := do
k ← positive <* spaces,
action_add k <|> action_del k

end lrat

/-- Match a proof in the LRAT format. -/
def lrat : parser proof.default.proof :=
many (lrat.action <* spaces)

end parser
end sat
