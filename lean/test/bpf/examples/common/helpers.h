#pragma once

typedef unsigned long long int u64;

/*
Copyright (c) 2021 The UNSAT Group. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luke Nelson, Xi Wang
*/

static u64 (*bpf_get_prandom_u32)(void) = (void *) 7;
