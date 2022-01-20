#include "tnum.h"
#include "serval.h"

/*
 * A very simple test driver. It assumes it will be passed four non-deterministic inputs, and
 * checks that tnum addition commutes over these inputs.
 */
int driver_main(void)
{
    u64 a, b, c, d;
    struct tnum x, y, xy, yx;
    a = serval_fresh_u64();
    b = serval_fresh_u64();
    c = serval_fresh_u64();
    d = serval_fresh_u64();

    x = (struct tnum) { a, b };
    y = (struct tnum) { c, d };

    xy = tnum_add(x, y);
    yx = tnum_add(y, x);

    serval_assert(xy.value == yx.value);
    serval_assert(xy.mask == yx.mask);
    return 0;
}
