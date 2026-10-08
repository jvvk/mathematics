"""Exact finite-n check for a general polygon K: smallest enclosing similar copy lam R_theta K + c (LP in (lam, c) for
each theta; theta searched near 0), then LP for a c (at optimal lam, theta) with every vertex of the copy inside K.
Usage: finite_K.py name n trials seed"""
import os, sys, signal, math, numpy as np
from scipy.optimize import linprog
from scipy.spatial import ConvexHull
import general_K as G
def _stop(*_): raise TimeoutError
signal.signal(signal.SIGALRM, _stop); signal.alarm(int(os.environ.get("TIME_LIMIT", "0")))
name, n, T, seed = sys.argv[1], int(sys.argv[2]), int(sys.argv[3]), int(sys.argv[4]); rng = np.random.default_rng(seed)
V = G.SHAPES[name]; V = V - V.mean(0)
d1, d2 = V[1] - V[0], V[2] - V[0]
if d1[0] * d2[1] - d1[1] * d2[0] < 0: V = V[::-1]
S = G.sides(V); U = np.array([s[0] for s in S]); H = np.array([s[1] for s in S])
R = lambda t: np.array([[math.cos(t), -math.sin(t)], [math.sin(t), math.cos(t)]])
def sample(m):
    lo, hi = V.min(0), V.max(0); out = np.empty((0, 2))
    while len(out) < m:
        x = rng.uniform(lo, hi, (4 * m, 2)); out = np.r_[out, x[(x @ U.T <= H).all(1)]]
    return out[:m]
def lam_of(X, t):
    Ut = U @ R(t).T; hx = (X @ Ut.T).max(0)            # support of points in rotated normals
    r = linprog([1, 0, 0], A_ub=-np.c_[H, Ut], b_ub=-hx, bounds=[(None, None)] * 3, method="highs"); return r.fun, hx, Ut
def ok(X, t):
    lam, hx, Ut = lam_of(X, t); W = (V @ R(t).T) * lam  # copy vertices before shift
    A = np.r_[-Ut, np.tile(U, (len(V), 1))]
    b = np.r_[lam * H - hx + 1e-12, (np.repeat(H[None], len(V), 0) - W @ U.T).reshape(-1)]
    return linprog([0, 0], A_ub=A, b_ub=b, bounds=[(None, None)] * 2, method="highs").status == 0
res = []
try:
    for _ in range(T):
        X = sample(n); X = X[ConvexHull(X).vertices]; f = lambda t: lam_of(X, t)[0]
        span = 60.0 / n; g = np.linspace(-span, span, 121); v = [f(t) for t in g]; i = int(np.argmin(v))
        a, b = g[max(i - 1, 0)], g[min(i + 1, 120)]
        for _ in range(45):
            m1, m2 = a + 0.382 * (b - a), a + 0.618 * (b - a)
            if f(m1) < f(m2): b = m2
            else: a = m1
        res.append(ok(X, (a + b) / 2))
except Exception as e: print("stopped:", type(e).__name__)
m = np.mean(res); print(f"finite {name} n={n}: trials={len(res)} P={m:.4f} +- {math.sqrt(m*(1-m)/len(res)):.4f}")
