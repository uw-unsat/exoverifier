/-
Copyright (c) 2021 The UNSAT Group. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luke Nelson, Xi Wang
-/
import tactic.basic
import data.num.basic

class hashable (α : Type*) :=
(hash : α → pos_num)

class perfect_hashable (α : Type*) extends hashable α :=
(hash_inj :
  ∀ {x y : α},
    hash x = hash y ↔ x = y)

instance : perfect_hashable pos_num :=
{ hash     := id,
  hash_inj := by tauto }

instance : perfect_hashable bool :=
{ hash     := λ b, cond b 1 2,
  hash_inj := λ x y, by cases x; cases y; tauto }
