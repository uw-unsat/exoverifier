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

## Running Exoverifier

### Building and testing

From the `lean` directory:

```sh
$ ./build-deps.sh # Build SAT solver dependencies under `pkgs`.
$ make bpf-examples # Use LLVM to build the BPF test programs.
$ leanpkg configure # Downloads and configures correct version of mathlib.
$ leanpkg build # Builds and checks proofs for mathlib and Exoverifier.
$ leanpkg test # Sanity test that checks the Lean files under `lean/test`.
```

### Generating and checking a safety proof for a simple BPF program

The following command uses the abstract interpretation library verifier to produce a proof
of safety for the BPF program `test/bpf/examples/absint/simple1.S`, writing the proof to `simple1.lef`.
(You can use "se+sat" instead of "absint" to generate the proof using the symbolic execution
library verifier instead.)
```sh
$ ./scripts/make_proof.py --verifier absint test/bpf/examples/absint/simple1.bin simple1.lef

# Expected output:
#  Generated proof at simple1.lef in 11.1s.
```

You can use Lean's builtin proof checker to validate the proof:
```sh
$ leanchecker simple1.lef test_bpf.program_safety

# Expected output:
#  axiom propext : Π {a b : Prop}, (a <-> b) -> a = b
#  axiom quot.sound : Π {α : Sort u}, Π {r : α -> α -> Prop}, Π {a b : α}, r a b -> quot.mk r a = quot.mk r b
#  axiom classical.choice : Π {α : Sort u}, nonempty α -> α
#  theorem test_bpf.program_safety : bpf.cfg.safe test_bpf.program
#  checked 6710 declarations
```

The axioms `leanchecker` reports are those introduced by Lean's standard library and by mathlib.
You can also check the validity of the proof using [Trepplein] or [Nanoda] (assuming they
are installed):

```sh
$ trepplein -p test_bpf.program_safety simple1.lef
$ nanoda 8 simple1.lef
```

### Generating a proof for a more complicated BPF program using symbolic execution

The symbolic execution library verifier is more general than the
abstract interpreter one, but produces larger and slower-to-check proofs.
As an example of a program that requires using the symbolic
execution library verifier, consider the following BPF program
(found in `test/bpf/examples/symeval/unreachable-division.S`):

```
    /* Innitialize r0 to a non-predictable value. */
    call BPF_GET_RANDOM_U32

    /* Set r1 = r0. */
    r1 = r0

    /* Check for r1 == 0. */
    if r1 == 0 goto out

    /* Perform a division using r0. */
    r0 /= r0
    out: exit
```

The abstract interpreter (and earlier versions of the Linux kernel verifier) fail to recognize this program as safe, as they do not track equality among registers.
While the verifier learns that r1 cannot be 0 after the jump, it fails
to learn that r0 cannot be 0 either, even though these registers must hold the same value. Therefore, the program is rejected due the possibility of an unsafe division by zero. This happens because these verifiers do not use relational domains for tracking
BPF register values.

The symbolic execution library verifier, on the other hand, is able to produce a proof for this program because r0 and r1 will be backed by the same SMT variables
after `r1 = r0`. When the solver searches for an assignment to this variable
that triggers a division by zero, it returns UNSAT which implies the program is safe.

You can generate a proof for this program using the symbolic execution library verifier
with the following:

```sh
$ ./scripts/make_proof.py --verifier se+sat test/bpf/examples/symeval/relational-check.bin relational-check.lef

# Expected output:
#  Generated proof at relational-check.lef in 12.8s.
```
You can use `leanchecker` or another proof checker to validate the resulting proof:

```sh
$ leanchecker relational-check.lef test_bpf.program_safety

# Expected output:
#  axiom propext : Π {a b : Prop}, (a <-> b) -> a = b
#  axiom quot.sound : Π {α : Sort u}, Π {r : α -> α -> Prop}, Π {a b : α}, r a b -> #  quot.mk r a = quot.mk r b
#  axiom classical.choice : Π {α : Sort u}, nonempty α -> α
#  theorem test_bpf.program_safety : bpf.cfg.safe test_bpf.program
#  checked 8045 declarations
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
