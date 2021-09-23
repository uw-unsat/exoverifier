#!/usr/bin/env python3

import argparse
import subprocess
import os, os.path, shutil, sys, tempfile

SOLVERS = {
    "lingeling": "-q -t {proof} {cnf}",
    "kissat": "-q {cnf} {proof}",
    "cadical": "-q {cnf} {proof}",
    "cryptominisat5": "--verb 0 {cnf} {proof}",
    "satch": "-q {cnf} {proof}",
    "picosat": "-r {proof} {cnf}",
}
DRAT_TRIM = "drat-trim"


def main():
    os.environ["PATH"] += os.pathsep + os.path.dirname(__file__)
    parser = argparse.ArgumentParser()
    parser.add_argument("--solver", default="lingeling")
    args = parser.parse_args()
    with tempfile.TemporaryDirectory() as tmpdir:
        cnf, proof, lrat = [os.path.join(tmpdir, s) for s in ["cnf", "proof", "lrat"]]
        with open(cnf, "wb") as f:
            f.write(sys.stdin.buffer.read())
        # Run the SAT solver.
        fmt = SOLVERS[os.path.basename(args.solver)].format(cnf=cnf, proof=proof)
        cp = subprocess.run(
            [shutil.which(args.solver)] + fmt.split(), capture_output=True
        )
        output = cp.stdout.strip()
        assert output == b"s UNSATISFIABLE", output
        # Run drat-trim.
        subprocess.run(
            [shutil.which(DRAT_TRIM), cnf, proof, "-O", "-L", lrat], capture_output=True
        )
        with open(lrat, "rb") as f:
            sys.stdout.buffer.write(f.read())


if __name__ == "__main__":
    main()
