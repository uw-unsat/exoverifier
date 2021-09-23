    if r1 == r2 goto l0
    exit
l0: if r1 == r2 goto l1
    r1 /= r3            // This unchecked division is safe because it's unreachable
l1: exit
