#!/usr/bin/env python3
# Copyright (c) 2021 The UNSAT Group. All rights reserved.
# Released under Apache 2.0 license as described in the file LICENSE.
# Authors: Luke Nelson, Xi Wang
import argparse
import subprocess
import shutil
import os


LEAN_EXE = shutil.which("lean")

THIS_DIR = os.path.dirname(__file__)


parser = argparse.ArgumentParser()
parser.add_argument(
    "--verifier",
    choices=["absint", "se+sat", "simple"],
    help="User-space verifier to use to generate proof",
    required=True,
)
parser.add_argument("program", type=str, help="Path to binary of BPF program")
parser.add_argument("output", type=str, help="Path to output proof to")
args = parser.parse_args()


VERIFIER_MAP = {
    "absint": "test/bpf/absint_harness.lean",
    "se+sat": "test/bpf/symeval_harness.lean",
    "simple": "test/bpf/simplechecker_harness.lean",
}


def produce_proof(verifier, program, outfile):
    harness_file = os.path.join(THIS_DIR, "..", VERIFIER_MAP[verifier])
    env = dict(os.environ)
    env.update({"BPF_BIN_PATH": program})
    subprocess.run(
        [
            LEAN_EXE,
            f"--export={outfile}",
            "--only-export=test_bpf.program_safety",
            "--tstack=64000",
            harness_file,
        ],
        check=True,
        env=env,
    )


produce_proof(args.verifier, args.program, args.output)
