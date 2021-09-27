/*
Copyright (c) 2021 The UNSAT Group. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luke Nelson, Xi Wang
*/

/* Example program using a bounded loop. */

    r1 = 5
a:  r1 -= 1
    if r1 == 0 goto a
    exit
