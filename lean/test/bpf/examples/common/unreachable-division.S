/*
Copyright (c) 2021 The UNSAT Group. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luke Nelson, Xi Wang
*/
#include <helpers.h>

/* A program which is safe because the unchecked division is not reachable. */

        // Set r6 and r7 to unpredictable values
        call BPF_GET_RANDOM_U32
        r6 = r0
        call BPF_GET_RANDOM_U32
        r7 = r0

        if r6 == r7 goto l0
        exit
l0:     if r7 == r6 goto l1
        r1 /= 0            // This division by zero is ok because it is not reachable
l1:     exit
