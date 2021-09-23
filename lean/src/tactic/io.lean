/-
Copyright (c) 2021 The UNSAT Group. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luke Nelson, Xi Wang
-/
import tactic.basic
import data.vector
import data.bitvec.basic
import bpf.basic
import bpf.decode
import bpf.cfg

/-!
# General-purpose tactics for obtaining values via IO.

This file contains tactics for obtaining values by performing IO;
for example, producing a string from the contents of a file or from an environment variable.
These use tactic.unsafe_run_io, so care must be taken that they are used in a situation where
the value being read is effectively constant: e.g., reading test files or environment variables
that are not changed during execution.
-/

namespace buffer

/-- Convert a char_buffer into a list of bytes represented as vector of bool. -/
def to_byte_list (x : char_buffer) : list (msbvector 8) :=
x.to_list.map $ λ (c : char), ↑(c.val)

end buffer

namespace tactic
namespace io

/-- Create an expression from running an io action. -/
meta def exact_io {α : Type} [has_reflect α] (x : io α) : tactic unit := do
v ← tactic.unsafe_run_io x,
tactic.exact `(v)

/-- A tactic that fills in a string using the value from an environment variable. -/
meta def from_env_var (s default : string) : tactic unit := do
var ← tactic.unsafe_run_io $ io.env.get s,
let v := var.get_or_else default in
tactic.exact `(v)

private def bytes_to_quadwords_le_aux : list (msbvector 8) → list (msbvector 64) → list (msbvector 64)
| (b₁ :: b₂ :: b₃ :: b₄ :: b₅ :: b₆ :: b₇ :: b₈ :: tail) rest :=
  let qw : msbvector 64 := b₈.append $ b₇.append $ b₆.append $ b₅.append $ b₄.append $ b₃.append $ b₂.append b₁ in
  bytes_to_quadwords_le_aux tail (qw :: rest)
| _ rest := rest

private def bytes_to_quadwords_le (l : list (msbvector 8)) : list (msbvector 64) :=
(bytes_to_quadwords_le_aux l []).reverse

private def flatten_quadwords : list (msbvector 64) → list bool
| []        := []
| (x :: xs) := x.1 ++ flatten_quadwords xs

/--
  Read the content of a file consisting of little-endian 64-bit values
  as a list of bits, where each chunk of 64 bits is given in decreasing significance.
-/
meta def read_le_quadword_file_as_be_bits (name : string) : io (list bool) := do
buf ← io.fs.read_file name tt,
let qws : list (msbvector 64) := bytes_to_quadwords_le buf.to_byte_list in
pure $ flatten_quadwords qws

meta def from_le_quadword_file_as_be_bits (name : string) : tactic unit := do
exact_io $ read_le_quadword_file_as_be_bits name

meta def read_le_quadword_file_as_bpf_program (name : string) : io bpf.cfg.trie_program := do
bits ← read_le_quadword_file_as_be_bits name,
match bpf.decode bits with
| none := io.fail "Failed to decode bits."
| some instrs := pure (bpf.cfg.trie_program.decode_from_flat instrs)
end

/-- Read the content of a file as a string. -/
meta def read_file_as_string (name : string) : io string := do
buf ← io.fs.read_file name,
pure buf.to_string

meta def from_file_as_string (name : string) : tactic unit :=
exact_io $ read_file_as_string name

end io
end tactic
