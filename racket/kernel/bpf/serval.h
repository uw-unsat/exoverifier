#pragma once
#include "types.h"

extern u64 serval_fresh_u64(void);

/*
 * For now, trap on assertion failure. Serval turns this into a "bug-on" and assertion in Rosette.
 * Later can write something for better error messages.
 */
static void __attribute__((noinline)) serval_assert(bool condition)
{
    if (!condition)
        __builtin_trap();
}
