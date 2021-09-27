/*
Copyright (c) 2021 The UNSAT Group. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luke Nelson, Xi Wang
*/

/* A program which is safe because the unchecked division is not reachable. */

        if r1 == r2 goto l0
        exit
l0:     if r1 == r2 goto l1
        r1 /= r3            // This unchecked division is safe because it's unreachable
l1:     exit
