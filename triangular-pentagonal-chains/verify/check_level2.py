import random
from math import isqrt
from assemble import chain, BEND
def tri(s): r = isqrt(8 * s + 1); return r * r == 8 * s + 1
rng = random.Random(7)
Ns = [49 * 2674 + 28, 49 * 2674 + 29, 49 * 2675 + 76] + [rng.randrange(131054, 400000) for _ in range(6)]
for N in Ns:
    C = chain(N)
    assert len(C) == N and len(set(C)) == N and min(C) == 1 and max(C) == N
    assert all((x + y) % 2 and tri(x + y) for x, y in zip(C, C[1:]))
    assert C[0] == 1 and C[-1] == BEND[N % 2]
    print("ok", N)
