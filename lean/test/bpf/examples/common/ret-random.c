/*
Copyright (c) 2021 The UNSAT Group. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luke Nelson, Xi Wang
*/

#include <helpers.h>

int main(void) {
    int x = bpf_get_prandom_u32();
    return x;
}
