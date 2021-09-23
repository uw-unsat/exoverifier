/-
Copyright (c) 2021 The UNSAT Group. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luke Nelson, Xi Wang
-/
import .io

namespace debug

/-- Dump a string to a file for debugging. -/
protected meta def dump_str_to_file (filename str : string) : io unit := do
fd ← io.mk_file_handle filename io.mode.write,
io.fs.write fd (string.to_char_buffer str),
io.fs.close fd

protected meta def dump_option_str_to_file (filename : string) (o : option string) : io unit :=
(sequence $ debug.dump_str_to_file filename <$> o) >> pure ()

end debug
