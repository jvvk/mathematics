"""Monte Carlo for the distribution of N, the number of the eight flipped tetrahedra with four acute faces."""
import numpy as np
from itertools import combinations, product

rng = np.random.default_rng(20261005)
M = 400_000
X = rng.normal(size=(M, 4, 3)); X /= np.linalg.norm(X, axis=2, keepdims=True)
N = np.zeros(M, dtype=int)
for s in product((1, -1), repeat=3):
    sig = np.array((1,) + s)[None, :, None]
    V = X * sig
    ok = np.ones(M, dtype=bool)
    for f in combinations(range(4), 3):
        for k in f:
            i, j = [x for x in f if x != k]
            ok &= np.einsum("mi,mi->m", V[:, i] - V[:, k], V[:, j] - V[:, k]) > 0
    N += ok
p = np.bincount(N, minlength=3) / M
print("P(N=0,1,2,...)=", np.round(p, 4), "mean N =", N.mean().round(4), "-> p est", (N.mean() / 8).round(5), "max N", N.max())
