# Copyright (c) 2021 The UNSAT Group. All rights reserved.
# Released under Apache 2.0 license as described in the file LICENSE.
# Authors: Luke Nelson, Xi Wang
import unittest
import glob
from test.bpf.test_bpf_checker import *

ABSINT_TEST_DIR = "test/bpf/examples/absint/"

TEST_FILES = [
    (name, not "fail" in name) for name in glob.glob(ABSINT_TEST_DIR + "*.bin")
]


class AbsintTest(BPFCheckerTest):
    LEAN_TEST_FILE = "test/bpf/absint_harness.lean"


def load_tests(loader, tests, pattern):
    tests = unittest.TestSuite()
    tests.addTests(
        [
            AbsintTest("run_test", file, expect_success)
            for (file, expect_success) in TEST_FILES
        ]
    )
    return tests
