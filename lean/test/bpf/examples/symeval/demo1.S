    r1 = r2
    if r1 == 0 goto l
    r3 /= r2           // Safe because r2 != 0, and r1 == r2
l:  exit
