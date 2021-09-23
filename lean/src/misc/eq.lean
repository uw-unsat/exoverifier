/-
Copyright (c) 2021 The UNSAT Group. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luke Nelson, Xi Wang
-/

theorem cond_fn_ext {α β : Type*} (b : bool) (f g : α → β) :
  (λ (x : α), cond b (f x) (g x)) = (cond b f g) :=
begin
  funext x,
  cases b; refl
end
