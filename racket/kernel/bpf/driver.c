#include "tnum.h"
#include "serval.h"

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
