# Copyright (c) 2021 The UNSAT Group. All rights reserved.
# Released under Apache 2.0 license as described in the file LICENSE.
# Authors: Luke Nelson, Xi Wang
import tempfile
import os
import unittest
import time
import timeit
import test.bpf.test_absint as test_absint

# r1 = 1
MOV_ONE = b"\xb7\x01\x00\x00\x01\x00\x00\x00"
# exit
EXIT = b"\x95\x00\x00\x00\x00\x00\x00\x00"

NITER = 50


class TestScale(unittest.TestCase):
    @staticmethod
    def prepare_test_bin(f, ninstrs):
        for i in range(ninstrs - 1):
            f.write(MOV_ONE)
        f.write(EXIT)
        f.flush()

    @staticmethod
    def run_once(f, ninstrs):
        TestScale.prepare_test_bin(f, ninstrs)
        return timeit.timeit(
            lambda: test_absint.AbsintTest(
                bpf_prog=f.name, expect_success=True
            ).run_test(),
            number=1,
        )

    def test_absint_scaling(self):
        with tempfile.NamedTemporaryFile(mode="wb") as f:
            for i in range(NITER):
                seconds = TestScale.run_once(f, i)
                print(f"{i} instructions, {round(seconds, 1)} seconds")


if __name__ == "__main__":
    unittest.main()
