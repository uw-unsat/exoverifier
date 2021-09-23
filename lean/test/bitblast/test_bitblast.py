# Copyright (c) 2021 The UNSAT Group. All rights reserved.
# Released under Apache 2.0 license as described in the file LICENSE.
# Authors: Luke Nelson, Xi Wang
import unittest
import subprocess
import os
import glob
import shutil
from unittest.util import strclass

LEAN_EXE = shutil.which("lean")
TEST_FILES = ["test/bitblast/add_comm.lean"]


class BitwidthTest(unittest.TestCase):
    def __init__(self, methodname="test_bitwidth", filename="", bitwidth=1):
        super().__init__(methodname)
        self.bitwidth = bitwidth
        self.filename = filename

    def test_bitwidth(self):
        env = dict(os.environ)
        env.update({"BITWIDTH": str(self.bitwidth)})
        p = subprocess.run([LEAN_EXE, "--tstack=12000", self.filename], env=env)
        self.assertEqual(p.returncode, 0)

    def __str__(self):
        return f"{self.filename},BITWIDTH={self.bitwidth} ({strclass(self.__class__)})"


def load_tests(loader, tests, pattern):
    bitwidths = range(1, 8)
    tests = unittest.TestSuite()
    tests.addTests(
        [
            BitwidthTest("test_bitwidth", file, bw)
            for file in TEST_FILES
            for bw in bitwidths
        ]
    )
    return tests
