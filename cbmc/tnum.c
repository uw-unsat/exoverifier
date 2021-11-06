#include <stdlib.h>
#include <stdint.h>
#include <stdbool.h>

typedef uint8_t u8;
typedef uint32_t u32;
typedef int32_t s32;
typedef uint64_t u64;
typedef int64_t s64;

struct tnum {
    u64 value;
    u64 mask;
};

u64 nondet_u64(void);

#define TNUM(_v, _m)    (struct tnum){.value = _v, .mask = _m}
/* A completely unknown value */
const struct tnum tnum_unknown = { .value = 0, .mask = -1 };

bool tnum_valid(struct tnum a)
{
    return (a.value & a.mask) == 0;
}

bool tnum_contains(struct tnum a, u64 constant)
{
    return (a.mask | ~(a.value ^ constant)) + 1 == 0;
}

/* Macro version of tnum_contains because CBMC disallows calling functions /
 * side effects within quantifiers.
 */
#define TNUM_CONTAINS(a, constant) ((a.mask | ~(a.value ^ constant)) + 1 == 0)

struct tnum nondet_tnum(void)
{
    u64 mu, v;
    struct tnum t;

    t = TNUM(nondet_u64(), nondet_u64());
    __CPROVER_assume(tnum_valid(t));

    return t;
}

struct tnum tnum_const(u64 value)
{
    return TNUM(value, 0);
}

#if 0
struct tnum tnum_range(u64 min, u64 max)
{
    u64 chi = min ^ max, delta;
    u8 bits = fls64(chi);

    /* special case, needed because 1ULL << 64 is undefined */
    if (bits > 63)
        return tnum_unknown;
    /* e.g. if chi = 4, bits = 3, delta = (1<<3) - 1 = 7.
     * if chi = 0, bits = 0, delta = (1<<0) - 1 = 0, so we return
     *  constant min (since min == max).
     */
    delta = (1ULL << bits) - 1;
    return TNUM(min & ~delta, delta);
}
#endif

struct tnum tnum_lshift(struct tnum a, u8 shift)
{
    return TNUM(a.value << shift, a.mask << shift);
}

struct tnum tnum_rshift(struct tnum a, u8 shift)
{
    return TNUM(a.value >> shift, a.mask >> shift);
}

struct tnum tnum_arshift(struct tnum a, u8 min_shift, u8 insn_bitness)
{
    /* if a.value is negative, arithmetic shifting by minimum shift
     * will have larger negative offset compared to more shifting.
     * If a.value is nonnegative, arithmetic shifting by minimum shift
     * will have larger positive offset compare to more shifting.
     */
    if (insn_bitness == 32)
        return TNUM((u32)(((s32)a.value) >> min_shift),
                (u32)(((s32)a.mask)  >> min_shift));
    else
        return TNUM((s64)a.value >> min_shift,
                (s64)a.mask  >> min_shift);
}

struct tnum tnum_add(struct tnum a, struct tnum b)
{
    u64 sm, sv, sigma, chi, mu;

    sm = a.mask + b.mask;
    sv = a.value + b.value;
    sigma = sm + sv;
    chi = sigma ^ sv;
    mu = chi | a.mask | b.mask;
    return TNUM(sv & ~mu, mu);
}

struct tnum tnum_sub(struct tnum a, struct tnum b)
{
    u64 dv, alpha, beta, chi, mu;

    dv = a.value - b.value;
    alpha = dv + a.mask;
    beta = dv - b.mask;
    chi = alpha ^ beta;
    mu = chi | a.mask | b.mask;
    return TNUM(dv & ~mu, mu);
}

struct tnum tnum_and(struct tnum a, struct tnum b)
{
    u64 alpha, beta, v;

    alpha = a.value | a.mask;
    beta = b.value | b.mask;
    v = a.value & b.value;
    return TNUM(v, alpha & beta & ~v);
}

struct tnum tnum_or(struct tnum a, struct tnum b)
{
    u64 v, mu;

    v = a.value | b.value;
    mu = a.mask | b.mask;
    return TNUM(v, mu & ~v);
}

struct tnum tnum_xor(struct tnum a, struct tnum b)
{
    u64 v, mu;

    v = a.value ^ b.value;
    mu = a.mask | b.mask;
    return TNUM(v & ~mu, mu);
}

/* Generate partial products by multiplying each bit in the multiplier (tnum a)
 * with the multiplicand (tnum b), and add the partial products after
 * appropriately bit-shifting them. Instead of directly performing tnum addition
 * on the generated partial products, equivalenty, decompose each partial
 * product into two tnums, consisting of the value-sum (acc_v) and the
 * mask-sum (acc_m) and then perform tnum addition on them. The following paper
 * explains the algorithm in more detail: https://arxiv.org/abs/2105.05398.
 */
struct tnum tnum_mul(struct tnum a, struct tnum b)
{
    u64 acc_v = a.value * b.value;
    struct tnum acc_m = TNUM(0, 0);

    while (a.value || a.mask) {
        /* LSB of tnum a is a certain 1 */
        if (a.value & 1)
            acc_m = tnum_add(acc_m, TNUM(0, b.mask));
        /* LSB of tnum a is uncertain */
        else if (a.mask & 1)
            acc_m = tnum_add(acc_m, TNUM(0, b.value | b.mask));
        /* Note: no case for LSB is certain 0 */
        a = tnum_rshift(a, 1);
        b = tnum_lshift(b, 1);
    }
    return tnum_add(TNUM(acc_v, 0), acc_m);
}

/* Note that if a and b disagree - i.e. one has a 'known 1' where the other has
 * a 'known 0' - this will return a 'known 1' for that bit.
 */
struct tnum tnum_intersect(struct tnum a, struct tnum b)
{
    u64 v, mu;

    v = a.value | b.value;
    mu = a.mask & b.mask;
    return TNUM(v & ~mu, mu);
}

struct tnum tnum_union(struct tnum a, struct tnum b)
{
    u64 v, mu;

    v = a.value | b.value;
    mu = a.mask | b.mask | (a.value ^ b.value);
    return TNUM(v & ~mu, mu);
}

struct tnum tnum_shl(struct tnum a, struct tnum b, u8 insn_bitness)
{
    u8 amt = 1;

    b = tnum_and(b, tnum_const(insn_bitness - 1));

    for (int i = 0; i < 6; i++) {

        if (b.mask & 1)
            a = tnum_union(a, tnum_lshift(a, amt));

        if (b.value & 1)
            a = tnum_lshift(a, amt);

        amt <<= 1;
        b = tnum_rshift(b, 1);
    }

    return a;
}

struct tnum tnum_lshr(struct tnum a, struct tnum b, u8 insn_bitness)
{
    u8 amt = 1;

    b = tnum_and(b, tnum_const(insn_bitness - 1));

    for (int i = 0; i < 6; i++) {

        if (b.mask & 1)
            a = tnum_union(a, tnum_rshift(a, amt));

        if (b.value & 1)
            a = tnum_rshift(a, amt);

        amt <<= 1;
        b = tnum_rshift(b, 1);
    }

    return a;
}

struct tnum tnum_cast(struct tnum a, u8 size)
{
    a.value &= (1ULL << (size * 8)) - 1;
    a.mask &= (1ULL << (size * 8)) - 1;
    return a;
}

bool tnum_is_aligned(struct tnum a, u64 size)
{
    if (!size)
        return true;
    return !((a.value | a.mask) & (size - 1));
}

bool tnum_in(struct tnum a, struct tnum b)
{
    if (b.mask & ~a.mask)
        return false;
    b.value &= ~a.mask;
    return a.value == b.value;
}

struct tnum tnum_subreg(struct tnum a)
{
    return tnum_cast(a, 4);
}

struct tnum tnum_clear_subreg(struct tnum a)
{
    return tnum_lshift(tnum_rshift(a, 32), 32);
}

struct tnum tnum_const_subreg(struct tnum a, u32 value)
{
    return tnum_or(tnum_clear_subreg(a), tnum_const(value));
}

#if 0
void check_tnum_or_optimal(void)
{
    struct tnum a, b, d;
    u64 z;

    a = nondet_tnum();
    b = nondet_tnum();
    d = nondet_tnum();
    z = nondet_u64();

    __CPROVER_assume(tnum_contains(tnum_or(a, b), z));
    __CPROVER_assume(!tnum_contains(d, z));

    __CPROVER_assert(
        __CPROVER_exists { u64 x;
            __CPROVER_exists { u64 y;
                TNUM_CONTAINS(a, x) &&
                TNUM_CONTAINS(b, y) &&
                !TNUM_CONTAINS(d, x | y)
            } }, "tnum_or optimality");
}
#endif

int main(int argc, char **argv) {

    struct tnum a, b, c;
    u64 x, y, z;

    a = nondet_tnum();
    b = nondet_tnum();
    x = nondet_u64();
    y = nondet_u64();

    __CPROVER_assume(tnum_contains(a, x));
    __CPROVER_assume(tnum_contains(b, y));

    __CPROVER_assert(tnum_valid(tnum_and(a, b)), "tnum_and valid");
    __CPROVER_assert(tnum_contains(tnum_and(a, b), x & y), "Test tnum_and");
    __CPROVER_assert(tnum_valid(tnum_add(a, b)), "tnum_add valid");
    __CPROVER_assert(tnum_contains(tnum_add(a, b), x + y), "Test tnum_add");
    __CPROVER_assert(tnum_valid(tnum_sub(a, b)), "tnum_sub valid");
    __CPROVER_assert(tnum_contains(tnum_sub(a, b), x - y), "Test tnum_sub");
    __CPROVER_assert(tnum_valid(tnum_or(a, b)), "tnum_or valid");
    __CPROVER_assert(tnum_contains(tnum_or(a, b), x | y), "Test tnum_or");
    __CPROVER_assert(tnum_valid(tnum_xor(a, b)), "tnum_xor valid");
    __CPROVER_assert(tnum_contains(tnum_xor(a, b), x ^ y), "Test tnum_xor");

    // __CPROVER_assume(y < 64);
    // __CPROVER_assert(tnum_valid(tnum_shl(a, b, 64)), "tnum_shl valid");
    // __CPROVER_assert(tnum_contains(tnum_shl(a, b, 64), x << y), "Test tnum_shl");
    // __CPROVER_assert(tnum_valid(tnum_lshr(a, b, 64)), "tnum_lshr valid");
    // __CPROVER_assert(tnum_contains(tnum_lshr(a, b, 64), x >> y), "Test tnum_lshr");

    return 0;
}