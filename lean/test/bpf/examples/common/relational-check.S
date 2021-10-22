/*
Copyright (c) 2021 The UNSAT Group. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luke Nelson, Xi Wang
*/
#include <helpers.h>

    /* Innitialize r0 to a non-predictable value. */
    call BPF_GET_RANDOM_U32

    /* Set r1 = r0. */
    r1 = r0

    /* Check for r1 == 0. */
    if r1 == 0 goto out

    /* Perform a division using r0. */
    r0 /= r0
    out: exit
