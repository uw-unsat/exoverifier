/*
Copyright (c) 2021 The UNSAT Group. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luke Nelson, Xi Wang
*/

/* A program that uses function calls. */

call 0x7 /* get_prandom_u32 */
r6 = r0
call 0x7 /* get_prandom_u32 */
r7 = r0
r6 += r7
r0 = r6
exit
