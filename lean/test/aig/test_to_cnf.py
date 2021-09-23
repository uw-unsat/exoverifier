# Copyright (c) 2021 The UNSAT Group. All rights reserved.
# Released under Apache 2.0 license as described in the file LICENSE.
# Authors: Luke Nelson, Xi Wang
from pathlib import Path
from unittest.util import strclass
import glob, shutil, subprocess
import unittest


PASS_TESTS = [
    "test/aig/c32sat/*.aig",
]

LEAN_EXE = shutil.which("lean")
LEAN_SRC = "test/aig/to_cnf.lean"


class TestToCNF(unittest.TestCase):
    def __init__(self, methodName="test_pass", path=None):
        super().__init__(methodName)
        self.path = path

    def __str__(self):
        return f"{self.path} ({strclass(self.__class__)})"

    def test_pass(self):
        data = Path(self.path).read_bytes()
        cp = subprocess.run(
            [LEAN_EXE, "--run", LEAN_SRC], input=data, capture_output=True
        )
        err = ("\n" + cp.stderr.strip().decode()) if cp.stderr else ""
        self.assertEqual(cp.returncode, 0, "non-zero exit status" + err)
        # Check the resulting CNF from AIG is UNSAT.
        cp = subprocess.run(["bin/sat.py"], input=cp.stdout, capture_output=True)
        self.assertEqual(cp.returncode, 0, cp.stderr)


def load_tests(loader, tests, pattern):
    suite = unittest.TestSuite()
    suite.addTests(
        [
            TestToCNF(path=path)
            for pattern in PASS_TESTS
            for path in sorted(glob.glob(pattern))
        ]
    )
    return suite


if __name__ == "__main__":
    unittest.main()
