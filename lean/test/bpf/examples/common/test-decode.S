r1 = 1
r1 += r2
r1 -= r2
r1 *= r2
r1 /= r2
r1 |= r2
r1 &= r2
r1 <<= r2
r1 >>= r2
r1 = -r1
r1 ^= r2
r1 = r2
r1 s>>= r2
*(u8 *)(r1 + 0) = r2
call 0x7
w1 = 0
w1 += w2
/* "ll" suffix denotes to use ld_imm64 instruction */
r1 = 0x42 ll
exit
