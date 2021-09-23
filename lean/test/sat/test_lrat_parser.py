# Copyright (c) 2021 The UNSAT Group. All rights reserved.
# Released under Apache 2.0 license as described in the file LICENSE.
# Authors: Luke Nelson, Xi Wang
from pathlib import Path
from unittest.util import strclass
import glob, shutil, subprocess
import unittest


PASS_TESTS = [
    "pkgs/drat-trim/examples/*.lrat",
]

LEAN_EXE = shutil.which("lean")
LEAN_SRC = "test/sat/lrat_parser.lean"


class TestLRATParser(unittest.TestCase):
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
        # Relax as the parser may reorder clause IDs or literals.
        def normalize(line):
            if line[1] == "d":
                return [line[:2], frozenset(line[2:])]
            else:
                i = line.index(b"0")
                return [line[0], frozenset(line[1:i]), line[i:]]

        act = [normalize(line.split()) for line in cp.stdout.splitlines()]
        exp = [normalize(line.split()) for line in data.splitlines()]
        self.assertEqual(act, exp)


def load_tests(loader, tests, pattern):
    suite = unittest.TestSuite()
    suite.addTests(
        [
            TestLRATParser(path=path)
            for pattern in PASS_TESTS
            for path in sorted(glob.glob(pattern))
        ]
    )
    return suite


if __name__ == "__main__":
    unittest.main()
