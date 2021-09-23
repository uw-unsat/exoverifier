/-
Copyright (c) 2021 The UNSAT Group. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luke Nelson, Xi Wang
-/
import aig.to_cnf
import aig.default

open aig
open aig.factory

local notation ⊥ := ref.bot
local notation ⊤ := ref.top

private def assert_true (s : state default.factory Prop) : Prop :=
(s.run factory.init).1

variables (a' b' c' d' : erased bool)

section O1

-- Neutrality

example : assert_true $ do
  a ← mk_var a',
  eq a <$> mk_and a ⊤ := rfl

example : assert_true $ do
  a ← mk_var a',
  eq a <$> mk_and ⊤ a := rfl

-- Boundedness

example : assert_true $ do
  a ← mk_var a',
  eq ⊥ <$> mk_and a ⊥ := rfl

example : assert_true $ do
  a ← mk_var a',
  eq ⊥ <$> mk_and ⊥ a := rfl

-- Idempotence

example : assert_true $ do
  a ← mk_var a',
  b ← pure a,
  eq a <$> mk_and a b := rfl

-- Contradiction

example : assert_true $ do
  a ← mk_var a',
  b ← pure $ -a,
  eq ⊥ <$> mk_and a b := rfl

end O1

section O2

-- Contradiction (A)

example : assert_true $ do
  a ← mk_var a', b ← mk_var b',
  c ← pure $ -a,
  eq ⊥ <$> (mjoin $ mk_and <$> mk_and a b <*> pure c) := rfl

example : assert_true $ do
  a ← mk_var a', b ← mk_var b',
  c ← pure $ -b,
  eq ⊥ <$> (mjoin $ mk_and <$> mk_and a b <*> pure c) := rfl

-- Contradiction (S)

example : assert_true $ do
  a ← mk_var a', b ← mk_var b', c ← mk_var c', d ← mk_var d',
  a ← pure $ -c,
  eq ⊥ <$> (mjoin $ mk_and <$> mk_and a b <*> mk_and c d) := rfl

example : assert_true $ do
  a ← mk_var a', b ← mk_var b', c ← mk_var c', d ← mk_var d',
  a ← pure $ -d,
  eq ⊥ <$> (mjoin $ mk_and <$> mk_and a b <*> mk_and c d) := rfl

example : assert_true $ do
  a ← mk_var a', b ← mk_var b', c ← mk_var c', d ← mk_var d',
  b ← pure $ -c,
  eq ⊥ <$> (mjoin $ mk_and <$> mk_and a b <*> mk_and c d) := rfl

example : assert_true $ do
  a ← mk_var a', b ← mk_var b', c ← mk_var c', d ← mk_var d',
  b ← pure $ -d,
  eq ⊥ <$> (mjoin $ mk_and <$> mk_and a b <*> mk_and c d) := rfl

example : assert_true $ do
  a ← mk_var a', b ← mk_var b', c ← mk_var c', d ← mk_var d',
  c ← pure $ -a,
  eq ⊥ <$> (mjoin $ mk_and <$> mk_and a b <*> mk_and c d) := rfl

example : assert_true $ do
  a ← mk_var a', b ← mk_var b', c ← mk_var c', d ← mk_var d',
  c ← pure $ -b,
  eq ⊥ <$> (mjoin $ mk_and <$> mk_and a b <*> mk_and c d) := rfl

example : assert_true $ do
  a ← mk_var a', b ← mk_var b', c ← mk_var c', d ← mk_var d',
  d ← pure $ -a,
  eq ⊥ <$> (mjoin $ mk_and <$> mk_and a b <*> mk_and c d) := rfl

example : assert_true $ do
  a ← mk_var a', b ← mk_var b', c ← mk_var c', d ← mk_var d',
  d ← pure $ -b,
  eq ⊥ <$> (mjoin $ mk_and <$> mk_and a b <*> mk_and c d) := rfl

-- Subsumption (A)

example : assert_true $ do
  a ← mk_var a', b ← mk_var b',
  c ← pure $ -a,
  eq c <$> (mjoin $ mk_and <$> (ref.neg <$> mk_and a b) <*> pure c) := rfl

example : assert_true $ do
  a ← mk_var a', b ← mk_var b',
  c ← pure $ -b,
  eq c <$> (mjoin $ mk_and <$> (ref.neg <$> mk_and a b) <*> pure c) := rfl

-- Subsumption (S)

example : assert_true $ do
  a ← mk_var a', b ← mk_var b', c ← mk_var c', d ← mk_var d',
  c ← pure $ -a,
  lhs ← mjoin $ mk_and <$> (ref.neg <$> mk_and a b) <*> mk_and c d,
  rhs ← mk_and c d,
  pure $ lhs = rhs := rfl

example : assert_true $ do
  a ← mk_var a', b ← mk_var b', c ← mk_var c', d ← mk_var d',
  d ← pure $ -a,
  lhs ← mjoin $ mk_and <$> (ref.neg <$> mk_and a b) <*> mk_and c d,
  rhs ← mk_and c d,
  pure $ lhs = rhs := rfl

example : assert_true $ do
  a ← mk_var a', b ← mk_var b', c ← mk_var c', d ← mk_var d',
  c ← pure $ -b,
  lhs ← mjoin $ mk_and <$> (ref.neg <$> mk_and a b) <*> mk_and c d,
  rhs ← mk_and c d,
  pure $ lhs = rhs := rfl

example : assert_true $ do
  a ← mk_var a', b ← mk_var b', c ← mk_var c', d ← mk_var d',
  d ← pure $ -b,
  lhs ← mjoin $ mk_and <$> (ref.neg <$> mk_and a b) <*> mk_and c d,
  rhs ← mk_and c d,
  pure $ lhs = rhs := rfl

-- Idempotence (A)

example : assert_true $ do
  a ← mk_var a', b ← mk_var b',
  c ← pure a,
  lhs ← mjoin $ mk_and <$> mk_and a b <*> pure c,
  rhs ← mk_and a b,
  pure $ lhs = rhs := rfl

example : assert_true $ do
  a ← mk_var a', b ← mk_var b',
  c ← pure b,
  lhs ← mjoin $ mk_and <$> mk_and a b <*> pure c,
  rhs ← mk_and a b,
  pure $ lhs = rhs := rfl

-- Resolution (S)

example : assert_true $ do
  a ← mk_var a', b ← mk_var b', c ← mk_var c', d ← mk_var d',
  a ← pure c, b ← pure $ -d,
  eq (-a) <$> (mjoin $ mk_and <$> (ref.neg <$> mk_and a b) <*> (ref.neg <$> mk_and c d)) := rfl

example : assert_true $ do
  a ← mk_var a', b ← mk_var b', c ← mk_var c', d ← mk_var d',
  a ← pure d, b ← pure $ -c,
  eq (-a) <$> (mjoin $ mk_and <$> (ref.neg <$> mk_and a b) <*> (ref.neg <$> mk_and c d)) := rfl

example : assert_true $ do
  a ← mk_var a', b ← mk_var b', c ← mk_var c', d ← mk_var d',
  b ← pure c, a ← pure $ -d,
  eq (-b) <$> (mjoin $ mk_and <$> (ref.neg <$> mk_and a b) <*> (ref.neg <$> mk_and c d)) := rfl

example : assert_true $ do
  a ← mk_var a', b ← mk_var b', c ← mk_var c', d ← mk_var d',
  b ← pure d, a ← pure $ -c,
  eq (-b) <$> (mjoin $ mk_and <$> (ref.neg <$> mk_and a b) <*> (ref.neg <$> mk_and c d)) := rfl

end O2

section O3

-- Substitution (A)

example : assert_true $ do
  a ← mk_var a', b ← mk_var b',
  c ← pure $ b,
  lhs ← mjoin $ mk_and <$> (ref.neg <$> mk_and a b) <*> pure c,
  rhs ← mk_and (-a) b,
  pure $ lhs = rhs := rfl

example : assert_true $ do
  a ← mk_var a', b ← mk_var b',
  c ← pure $ a,
  lhs ← mjoin $ mk_and <$> (ref.neg <$> mk_and a b) <*> pure c,
  rhs ← mk_and (-b) a,
  pure $ lhs = rhs := rfl

example : assert_true $ do
  a ← mk_var a', b ← mk_var b',
  c ← pure $ b,
  lhs ← mjoin $ mk_and c <$> (ref.neg <$> mk_and a b),
  rhs ← mk_and (-a) b,
  pure $ lhs = rhs := rfl

example : assert_true $ do
  a ← mk_var a', b ← mk_var b',
  c ← pure $ a,
  lhs ← mjoin $ mk_and c <$> (ref.neg <$> mk_and a b),
  rhs ← mk_and (-b) a,
  pure $ lhs = rhs := rfl

-- Substitution (S)

example : assert_true $ do
  a ← mk_var a', b ← mk_var b', c ← mk_var c', d ← mk_var d',
  c ← pure b,
  lhs ← mjoin $ mk_and <$> (ref.neg <$> mk_and a b) <*> mk_and c d,
  rhs ← mjoin $ mk_and (-a) <$> mk_and c d,
  pure $ lhs = rhs := rfl

example : assert_true $ do
  a ← mk_var a', b ← mk_var b', c ← mk_var c', d ← mk_var d',
  c ← pure a,
  lhs ← mjoin $ mk_and <$> (ref.neg <$> mk_and a b) <*> mk_and c d,
  rhs ← mjoin $ mk_and (-b) <$> mk_and c d,
  pure $ lhs = rhs := rfl

example : assert_true $ do
  a ← mk_var a', b ← mk_var b', c ← mk_var c', d ← mk_var d',
  c ← pure b,
  lhs ← mjoin $ mk_and <$> mk_and c d <*> (ref.neg <$> mk_and a b),
  rhs ← mjoin $ mk_and (-a) <$> mk_and c d,
  pure $ lhs = rhs := rfl

example : assert_true $ do
  a ← mk_var a', b ← mk_var b', c ← mk_var c', d ← mk_var d',
  c ← pure a,
  lhs ← mjoin $ mk_and <$> mk_and c d <*> (ref.neg <$> mk_and a b),
  rhs ← mjoin $ mk_and (-b) <$> mk_and c d,
  pure $ lhs = rhs := rfl

end O3

section O4

-- Idempotence (S)

example : assert_true $ do
  a ← mk_var a', b ← mk_var b', c ← mk_var c', d ← mk_var d',
  a ← pure c,
  lhs ← mjoin $ mk_and <$> mk_and a b <*> mk_and c d,
  rhs ← mjoin $ mk_and d <$> mk_and a b,
  pure $ lhs = rhs := rfl

example : assert_true $ do
  a ← mk_var a', b ← mk_var b', c ← mk_var c', d ← mk_var d',
  b ← pure c,
  lhs ← mjoin $ mk_and <$> mk_and a b <*> mk_and c d,
  rhs ← mjoin $ mk_and d <$> mk_and a b,
  pure $ lhs = rhs := rfl

example : assert_true $ do
  a ← mk_var a', b ← mk_var b', c ← mk_var c', d ← mk_var d',
  a ← pure d,
  lhs ← mjoin $ mk_and <$> mk_and a b <*> mk_and c d,
  rhs ← mjoin $ mk_and c <$> mk_and a b,
  pure $ lhs = rhs := rfl

example : assert_true $ do
  a ← mk_var a', b ← mk_var b', c ← mk_var c', d ← mk_var d',
  b ← pure d,
  lhs ← mjoin $ mk_and <$> mk_and a b <*> mk_and c d,
  rhs ← mjoin $ mk_and c <$> mk_and a b,
  pure $ lhs = rhs := rfl

end O4

section hashing

-- Structural hashing

example : assert_true $ do
  a ← mk_var a',
  b ← mk_var b',
  ab ← mk_and a b,
  ba ← mk_and b a,
  ab' ← mk_and a b,
  ba' ← mk_and b a,
  pure $ ab = ab' ∧ ab = ba ∧ ab = ba' := ⟨rfl, ⟨rfl, rfl⟩⟩

end hashing
