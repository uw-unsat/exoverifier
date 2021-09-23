    r1 = r2
    r1 ^= 1
    if r1 == 1 goto l
    r3 /= r2           // Safe because r1 != 1, and r1 == r2 ^ 1
l:  exit
