/*
Copyright (c) 2021 The UNSAT Group. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luke Nelson, Xi Wang
*/

r1 += r1    // Add r1 to itself: r1 even
r1 += 1     // Add 1 to r1: r1 odd
r3 /= r1    // r1 must be odd, therefore non-zero, therefore division is safe
exit
