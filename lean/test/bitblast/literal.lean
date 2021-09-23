/-
Copyright (c) 2021 The UNSAT Group. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luke Nelson, Xi Wang
-/
import sat.bool
import smt.bitblast.basic
import smt.bitblast.default
import data.bitvec.basic

namespace literal_test
open smt.add_factory smt.const_factory smt.var_factory factory.trivial smt.bitblast

abbreviation β : Type := Σ n, vector bool n
abbreviation γ : Type := punit

def three : lsbvector 4 := vector.of_fn 3
def four  : lsbvector 4 := vector.of_fn 4

/-- Example of using trivial instance with monads on top of SMT interface. -/
def monad_example : state γ β := do
x : β ← smt.const_factory.mk_const three,
y : β ← smt.const_factory.mk_const four,
mk_add x y

/-- Example of using trivial instance without monads on top of SMT interface. -/
def pure_example : β :=
runtriv $ mk_add (runtriv (mk_const four)) $ runtriv (mk_const three)

/-- The two versions are equivalent (and addition commutes for 3 and 4). -/
example : runtriv monad_example = pure_example := rfl

/- Next, an example of using the low-level bitblasting implementation to get typed
   (and fast) implementations of bitvector operations over literals. -/

def circuit_adder {n : ℕ} (x y : vector bool n) : vector bool n := do
((smt.bitblast.mk_add x y).run punit.star).1.1

theorem circuit_adder_sound {n : ℕ} {x y : vector bool n} :
  (circuit_adder x y).nth = x.nth + y.nth :=
begin
  simp only [circuit_adder],
  rcases mk : (smt.bitblast.mk_add x y).run punit.star with ⟨⟨_, _⟩, ⟨⟩⟩,
  obtain ⟨h, -⟩ := eval_mk_add mk (by rw [eval.iff_trivial]) (by rw [eval.iff_trivial]),
  rw [eval.iff_trivial] at h,
  rw [h]
end

#eval (@circuit_adder 4 4 3).nth

#eval (@circuit_adder 64 50000 60000).nth

example : @circuit_adder 64 12345 678910 = @circuit_adder 64 678910 12345 := rfl

end literal_test
