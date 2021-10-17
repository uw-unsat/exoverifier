/*
Copyright (c) 2021 The UNSAT Group. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luke Nelson, Xi Wang
*/

/* A program which is safe because the unchecked division is not reachable. */

        // Set r3, r6, and r7 to non-deterministic values
        call 0x7 /* get_prandom_u32 */
        r6 = r0
        call 0x7 /* get_prandom_u32 */
        r7 = r0
        call 0x7 /* get_prandom_u32 */
        r3 = r0

        r0 = 0
        if r6 == r7 goto l0
        exit
l0:     if r7 == r6 goto l1
        r1 /= r3            // This unchecked division is safe because it's unreachable
l1:     exit
