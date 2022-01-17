#include <stdbool.h>

typedef unsigned long u64;

struct tnum {
    u64 value, mask;
};

extern struct tnum tnum_add(struct tnum a, struct tnum b);

/*
 * For now, trap on assertion failure. Serval turns this into a "bug-on" and assertion in Rosette.
 * Later can write something for better error messages.
 */
static void __attribute__((noinline)) serval_assert(bool condition)
{
    if (!condition)
        __builtin_trap();
}

/*
 * A very simple test driver. It assumes it will be passed four non-deterministic inputs, and
 * checks that tnum addition commutes over these inputs.
 */
int driver_main(u64 a, u64 b, u64 c, u64 d)
{
    struct tnum xy, yx;
    struct tnum x = { a, b };
    struct tnum y = { c, d };

    xy = tnum_add(x, y);
    yx = tnum_add(y, x);

    serval_assert(xy.value == yx.value);
    serval_assert(xy.mask == yx.mask);
    return 0;
}
