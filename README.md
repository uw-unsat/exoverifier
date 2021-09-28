# Exoverifier

Exoverifier is a prototype proof-carrying code framework for BPF programs.
It contains a specification of the BPF semantics and a safety definition, and
two automated proof generators implemented in Lean that produce proofs that specific BPF programs
meet the safety definition. The first is based on abstract interpretation and is inspired by the current BPF verifier in the Linux kernel. The second uses symbolic execution and an external SAT solver
to prove safety. Both can produce proofs in Lean's [proof export format](https://github.com/leanprover/lean/blob/master/doc/export_format.md), which can be checked by Lean's built-in proof checker or by external proof checkers like [Nanoda] or [Trepplein].

**This is a work in progress and should be treated as experimental. Our code
and tests may not work on your machine, and it should not yet be relied upon
for any purpose.**

## Requirements

- [Lean] community edition, v3.33.0c
- A recent version of [LLVM]
- Python3 (for running unit tests)

## Structure

- `lean/src` : Source code and proofs for Exoverifier, including BPF semantics / safety specification and proof generators / library verifiers.
- `lean/test` : Lean test files and python scripts to run tests.
- `lean/pkgs` : External dependencies, e.g., SAT solvers.

## Examples

### Building and testing

From the `lean` directory:

```sh
$ ./build-deps.sh # Build SAT solver dependencies under `pkgs`.
$ make bpf-examples # Use LLVM to build the BPF test programs.
$ leanpkg configure # Downloads and configures correct version of mathlib.
$ leanpkg build # Builds and checks proofs for mathlib and Exoverifier.
$ leanpkg test # Runs Lean test files under `lean/test`.
```

### Generating and checking proofs

Export a proof of safety for the BPF program `test/bpf/examples/absint/simple1.S` to `simple1.lef`, generating the proof using abstract interpretation. Use "se+sat" instead of "absint" to use the symbolic execution / SAT solver-based proof generator.
```sh
$ ./scripts/make_proof.py --verifier absint test/bpf/examples/absint/simple1.bin simple1.lef
```

Check the proof using the built-in checker from Lean:
```sh
$ leanchecker simple1.lef test_bpf.program_safety

# Expected output:
#  axiom propext : Π {a b : Prop}, (a <-> b) -> a = b
#  axiom quot.sound : Π {α : Sort u}, Π {r : α -> α -> Prop}, Π {a b : α}, r a b -> quot.mk r a = quot.mk r b
#  axiom classical.choice : Π {α : Sort u}, nonempty α -> α
#  theorem test_bpf.program_safety : bpf.cfg.safe test_bpf.program
#  checked 5887 declarations
```

Check the proof using [Trepplein] (requires it to be installed):
```sh
$ trepplein -p test_bpf.program_safety simple1.lef

# Expected output:
#  axiom propext {a b : Prop} (ᾰ : a ↔ b) : a = b
#
#  axiom {u} classical.choice {α : Sort u} (ᾰ : nonempty α) : α
#
#  axiom {u} quot.sound {α : Sort u} {r : (∀ (ᾰ_0 ᾰ_1 : α), Prop)} {a b : α}
#      (ᾰ : r a b) :
#    quot.mk r a = quot.mk r b
#
#  lemma test_bpf.program_safety : bpf.cfg.safe test_bpf.program :=
#  _
#
#  -- successfully checked 5887 declarations
```

Checking the proof using [Nanoda] (requires it to be installed):
```sh
$ nanoda 8 simple1.lef

# Expected output:
#  Successfully checked 5887 declarations!
#  Checked 5887 declarations in 7.633744416s
```

## Running Python tests

From the `lean` directory, after building dependencies:

```sh
$ python3 -m unittest discover -vv test
```

Or, if you have the [Green] test runner installed:

```sh
$ green -vv -f test
```

## License

Code under `lean/pkgs` maintains the licenses of the original packages:

- `lean/pkgs/aiger/LICENSE`
- `lean/pkgs/c32sat/LICENSE`
- `lean/pkgs/c32sat/src/LICENSE`
- `lean/pkgs/c32sat/src/test/LICENSE`
- `lean/pkgs/c32sat/tools/cnf2c32sat/LICENSE`
- `lean/pkgs/c32sat/xc32sat/LICENSE`
- `lean/pkgs/drat-trim/LICENSE`
- `lean/pkgs/druplig/LICENSE`
- `lean/pkgs/nanoda_lib/LICENSE`
- `lean/pkgs/picosat/LICENSE`
- `lean/pkgs/ubpf/LICENSE-APACHE`

Test BPF programs under `lean/test/bpf/examples/ebpf-samples` are copyrighted under their original sources (obtained from <https://github.com/vbpf/ebpf-samples>).

Remaining code is copyright 2021 The UNSAT Group 2021,
Released under the Apache 2.0 license as described in the file LICENSE.

[Green]: https://github.com/CleanCut/green
[Lean]: https://github.com/leanprover-community/lean
[LLVM]: https://llvm.org/
[Nanoda]: https://github.com/ammkrn/nanoda_lib
[Trepplein]: https://github.com/gebner/trepplein
