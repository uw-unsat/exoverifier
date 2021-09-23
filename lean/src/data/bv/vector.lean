/-
Copyright (c) 2021 The UNSAT Group. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luke Nelson, Xi Wang
-/
import .basic
import data.vector
import data.vector.basic
import data.bitvec.basic
import misc.vector

/--
A vector of bits where the MSB is at index 0.
This is the default interpretation under Lean's `data.bitvec`, so it is simply an
abbreviation.
-/
abbreviation msbvector (n : ℕ) : Type := vector bool n

/--
A vector of bits where the LSB is at index 0.
Can be used interchangably with `msbvector` and `vector bool`, it exists only to document intent.
-/
abbreviation lsbvector (n : ℕ) : Type := vector bool n
