"""Exact-as-possible optimisation of the lower-bound recursion (see lower.py docstring).
Uses a Dirichlet-parametrised simplex grid plus scipy local refinement of the worst points."""
import numpy as np
from scipy.optimize import minimize

def opts(x, a, c):
    x = np.clip(x, 0, None); x = x / x.sum(axis=-1, keepdims=True)
    x1, x2, x3, x4 = np.moveaxis(x, -1, 0)
    return np.max(np.stack([
        4**c * (x1**a + x4**a), 4**c * (x2**a + x3**a),
        2**c * (x1 + x2) ** a, 2**c * (x3 + x4) ** a,
        2**c * (x1 + x3) ** a, 2**c * (x2 + x4) ** a]), axis=0)

N = 48
pts = np.array([(i, j, k, N - i - j - k) for i in range(N + 1) for j in range(N + 1 - i)
                for k in range(N + 1 - i - j)], float) / N

def worst(a, c):
    v = opts(pts, a, c)
    idx = np.argsort(v)[:8]
    best = v[idx[0]]
    for i in idx:   # refine
        r = minimize(lambda y: opts(np.abs(y)[None, :], a, c)[0], pts[i] + 1e-9, method="Nelder-Mead",
                     options=dict(xatol=1e-10, fatol=1e-12, maxiter=4000))
        best = min(best, r.fun)
    return best

res = []
for a in np.arange(0.30, 0.62, 0.02):
    lo, hi = 0.0, a / 2
    for _ in range(28):
        mid = (lo + hi) / 2
        if worst(a, mid) >= 1: hi = mid
        else: lo = mid
    res.append((a - 2 * hi, a, hi))
    print(f"a={a:.2f} c={hi:.5f} exponent={a - 2*hi:.5f}", flush=True)
print("best", max(res))
