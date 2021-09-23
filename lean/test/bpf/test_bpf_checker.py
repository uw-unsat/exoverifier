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


class BPFCheckerTest(unittest.TestCase):
    def __init__(self, methodname="run_test", bpf_prog="", expect_success=True):
        super().__init__(methodname)
        self.bpf_prog = bpf_prog
        self.expect_success = expect_success

    def run_test(self):
        env = dict(os.environ)
        env.update({"BPF_BIN_PATH": str(self.bpf_prog)})
        p = subprocess.run(
            [LEAN_EXE, "--tstack=32000", self.LEAN_TEST_FILE],
            capture_output=True,
            encoding="utf8",
            env=env,
        )
        if self.expect_success:
            self.assertEqual(p.returncode, 0, "non-zero exit: " + p.stderr + p.stdout)
        else:
            self.assertNotEqual(p.returncode, 0, "exit status 0 when failure expected")

    def __str__(self):
        return f"{self.bpf_prog} ({strclass(self.__class__)})"
