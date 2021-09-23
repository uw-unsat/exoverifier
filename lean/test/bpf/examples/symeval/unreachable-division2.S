    if r1 <= r2 goto l1
    if r1 > r2 goto l1
    r1 /= r3            // This unchecked division is safe because it's not reachable.
l1: exit
