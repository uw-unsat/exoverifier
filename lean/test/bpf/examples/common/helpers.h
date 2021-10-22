#pragma once

/*
Copyright (c) 2021 The UNSAT Group. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luke Nelson, Xi Wang
*/

#define BPF_GET_RANDOM_U32 0x7

#if !defined(__ASSEMBLER__)

typedef signed int s32;
typedef unsigned int u32;
typedef signed long long int s64;
typedef unsigned long long int u64;

static u64 (*bpf_get_prandom_u32)(void) = (void *) BPF_GET_RANDOM_U32;

/* Create an optimization barrier for the variable "id" to avoid LLVM reasoning about its value. */
#define OPT_BARRIER(id) asm volatile("" : "+r" (id))

/* Abort by dividing by zero. */
static inline __attribute__((always_inline)) void abort(void) {
    asm volatile("r0 /= 0");
}

#endif