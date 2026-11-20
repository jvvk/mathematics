"""End-to-end: every C_N for 54 <= N <= LIMIT is a permutation of [1..N], adjacent sums odd triangular,
starts at 1, ends at b(N), and 1 + b(N) is triangular (so it closes to a necklace)."""
import sys
from math import isqrt
from assemble import chain, BEND

def tri(s): r = isqrt(8 * s + 1); return r * r == 8 * s + 1

LIMIT = int(sys.argv[1])
for N in range(54, LIMIT + 1):
    C = chain(N)
    assert len(C) == N and set(C) == set(range(1, N + 1)), N
    assert all((x + y) % 2 == 1 and tri(x + y) for x, y in zip(C, C[1:])), N
    assert C[0] == 1 and C[-1] == BEND[N % 2] and tri(C[0] + C[-1]), N
print("OK: aligned chains + necklaces for all 54 <=", "N <=", LIMIT)
