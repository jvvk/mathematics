"""Direct simulation of MO 458571 (exact geometry, no limit model), triangle and square, many trials.
For each sample: support values over a grid of rotation angles near 0 (vectorised), golden refinement of the best angle,
exact smallest enclosing copy at that angle, exact test whether some optimal copy lies inside K
(square: the copy may slide along its slack direction).  Usage: direct.py p n trials seed"""
import os, sys, signal, math, numpy as np
from scipy.spatial import ConvexHull
class Budget(Exception): pass
def _al(*_): raise Budget
signal.signal(signal.SIGALRM, _al); signal.alarm(int(os.environ.get("TIME_LIMIT", "0")))
p, n, T, seed = map(int, sys.argv[1:5]); rng = np.random.default_rng(seed)
if p == 3:
    N0 = np.array([[math.cos(a), math.sin(a)] for a in np.radians([90, 210, 330])])   # K: x.n <= 1 (inradius 1)
    box = 2.0
else:
    N0 = np.array([[1, 0], [0, 1], [-1, 0], [0, -1.0]]); box = 1.0
def sample():
    out = np.empty((0, 2))
    while len(out) < n:
        x = rng.uniform(-box, box, (2 * n, 2)); out = np.r_[out, x[(x @ N0.T <= 1).all(1)]]
    return out[:n]
def rot(t): c, s = np.cos(t), np.sin(t); return np.array([[c, -s], [s, c]])
def size(H, t):  # vectorised over t (array): objective
    ang = np.atleast_1d(t)[:, None] + np.arctan2(N0[:, 1], N0[:, 0])[None]
    U = np.stack([np.cos(ang), np.sin(ang)], -1)            # (G, m, 2)
    h = np.einsum('pd,gmd->gpm', H, U).max(1)                # (G, m)
    if p == 3: return h.sum(1), h, U
    return np.maximum(h[:, 0] + h[:, 2], h[:, 1] + h[:, 3]), h, U
def fits(H):
    span = min(60.0 / n, math.pi / p); g = np.linspace(-span, span, 241)
    v = size(H, g)[0]; i = int(np.argmin(v)); a, b = g[max(i - 1, 0)], g[min(i + 1, 240)]
    f = lambda t: size(H, t)[0][0]
    for _ in range(50):
        m1, m2 = a + 0.382 * (b - a), a + 0.618 * (b - a)
        if f(m1) < f(m2): b = m2
        else: a = m1
    t = (a + b) / 2; S, h, U = size(H, t); h = h[0]; U = U[0]
    if p == 3:   # enclosing triangle = the three support lines; corners = pairwise intersections
        C = np.array([np.linalg.solve(np.array([U[k], U[(k + 1) % 3]]), [h[k], h[(k + 1) % 3]]) for k in range(3)])
        return bool((C @ N0.T <= 1 + 1e-12).all())
    # square: side S = max widths; along the wider pair the position is fixed, along the other it may slide
    S = S[0]; w = [h[0] + h[2], h[1] + h[3]]; big = 0 if w[0] >= w[1] else 1; sm = 1 - big
    cb = (h[big] - h[big + 2]) / 2                           # centre coordinate along U[big] (fixed)
    lo, hi = h[sm] - S / 2, S / 2 - h[sm + 2]                # centre coordinate along U[sm] may lie in [lo, hi]
    corners_rel = np.array([[sx, sy] for sx in (-1, 1) for sy in (-1, 1)]) * S / 2   # in (U[big], U[sm]) frame
    E = np.array([U[big], U[sm]])                             # rows: frame vectors
    # corner = (cb + a1) U[big] + (y + a2) U[sm];  need corner . N0_j <= 1 for all j: linear in y
    ylo, yhi = lo, hi
    for a1, a2 in corners_rel:
        for nj in N0:
            coef = U[sm] @ nj; rhs = 1 - (cb + a1) * (U[big] @ nj) - a2 * coef
            if abs(coef) < 1e-15:
                if rhs < -1e-12: return False
            elif coef > 0: yhi = min(yhi, rhs / coef)
            else: ylo = max(ylo, rhs / coef)
    return ylo <= yhi + 1e-12
res = []
try:
    for _ in range(T):
        X = sample(); res.append(fits(X[ConvexHull(X).vertices] if n >= 3 else X))
except Budget: pass
k, m = len(res), sum(res); print(f"p={p} n={n} trials={k} hits={m} P={m/k:.4f} +- {math.sqrt(m/k*(1-m/k)/k):.4f}")
