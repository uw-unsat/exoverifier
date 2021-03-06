#!/usr/bin/env python3
# Copyright (c) 2021 The UNSAT Group. All rights reserved.
# Released under Apache 2.0 license as described in the file LICENSE.
# Authors: Luke Nelson, Xi Wang
import argparse
import subprocess
import shutil
import os
import time


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
    start_time = time.time()
    harness_file = os.path.join(THIS_DIR, "..", VERIFIER_MAP[verifier])
    env = dict(os.environ)
    env.update({"BPF_BIN_PATH": program})
    subprocess.run(
        [
            LEAN_EXE,
            f"--export={outfile}",
            "--only-export=test_bpf.program_safety",
            "--tstack=256000",
            harness_file,
        ],
        check=True,
        env=env,
    )
    end_time = time.time()
    print(f'Generated proof at {outfile} in {(end_time-start_time):3.1f}s.')


produce_proof(args.verifier, args.program, args.output)
