/*
Copyright (c) 2021 The UNSAT Group. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luke Nelson, Xi Wang
*/

#include <helpers.h>

int main(void) {
    unsigned long int x, y;

    x = bpf_get_prandom_u32();
    y = bpf_get_prandom_u32();

    if (x < y) {
        OPT_BARRIER(x);
        if (x > y) {
            abort();
        }
    }

    return 0;
}
