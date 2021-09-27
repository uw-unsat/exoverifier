/*
Copyright (c) 2021 The UNSAT Group. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luke Nelson, Xi Wang
*/

        r1 = r2
        if r1 == 0 goto l
        r3 /= r2           // Safe because r2 != 0, and r1 == r2
l:      exit
