/*
Copyright (c) 2021 The UNSAT Group. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luke Nelson, Xi Wang
*/

        if r1 <= r2 goto l1
        if r1 > r2 goto l1
        r1 /= r3            // This unchecked division is safe because it's not reachable.
l1:     exit
