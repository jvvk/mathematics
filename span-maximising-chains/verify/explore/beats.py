"""For a candidate, find arrangements that beat it on EVERY sampled valid input (exploration, MO 442949).
Usage: python beats.py n p q samples"""
import sys
import numpy as np
from hunt import all_classes, spans2

n = int(sys.argv[1]); tp = tuple(int(c) for c in sys.argv[2]); tq = tuple(int(c) for c in sys.argv[3])
N = int(sys.argv[4])
C = all_classes(n); P = np.array([c[0] for c in C]); Q = np.array([c[1] for c in C])
rng = np.random.default_rng(7)
always = np.ones(len(C), bool)
for s in range(N):
    L = np.sort(rng.exponential(1, n) ** rng.uniform(0.2, 3)) + 1e-9 * np.arange(n)
    A = np.sort(rng.exponential(1, n - 1) ** rng.uniform(0.2, 3)); A = A / A.sum() * rng.uniform(0.01, np.pi / 2)
    s2 = spans2(L, A, P, Q)
    t = spans2(L, A, np.array([tp]), np.array([tq]))[0]
    always &= s2 > t * (1 + 1e-12)
print(sum(always), "arrangements beat the candidate on all", N, "samples:")
for i in np.where(always)[0][:10]:
    print("  ", "".join(map(str, C[i][0])), "".join(map(str, C[i][1])))
