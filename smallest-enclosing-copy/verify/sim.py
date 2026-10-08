"""MO 458571: n uniform points in a regular p-gon K (inradius 1); smallest enclosing regular p-gon Q (any rotation);
P(Q can be placed inside K). Two independent methods.

finite: exact. For each rotation theta, r(theta) = min_c max_k (h_k(theta) - c.u_k(theta)) is an LP (support values of
the hull in the p rotated side normals). Minimise over theta (grid + golden refine). Then, among optimal centres, an LP
asks for one with every vertex of Q inside K.
limit (n -> inf): side k carries a Poisson process (D = scaled depth, s = position along the side, |s| <= L/2);
h_k ~ 1 + (1/n) max (Theta s - D). One LP in (rho, Theta, C): min rho s.t. rho + C.u_k >= Theta s_i - D_i.
Q inside K  <=>  exists optimal C with rho + C.u_k <= -|Theta| L/2 for all k.
Usage: sim.py finite p n trials seed | sim.py limit p trials seed"""
import os, sys, signal, math, numpy as np
from scipy.optimize import linprog
from scipy.spatial import ConvexHull
def _stop(*_): raise TimeoutError
signal.signal(signal.SIGALRM, _stop); signal.alarm(int(os.environ.get("TIME_LIMIT", "0")))

def normals(p, th=0.0):
    a = th + 2 * np.pi * np.arange(p) / p
    return np.c_[np.cos(a), np.sin(a)]

def verts(p, th=0.0):   # vertices of the regular p-gon with inradius 1 and side normals at th + 2 pi k/p
    a = th + np.pi / p + 2 * np.pi * np.arange(p) / p
    return np.c_[np.cos(a), np.sin(a)] / math.cos(math.pi / p)

def sample(p, n, rng):
    V = verts(p); out = np.empty((0, 2))
    while len(out) < n:
        x = rng.uniform(-1 / math.cos(math.pi / p), 1 / math.cos(math.pi / p), (2 * n, 2))
        x = x[(x @ normals(p).T <= 1).all(1)]; out = np.r_[out, x]
    return out[:n]

def r_of(H, p, th):     # LP: min r s.t. r + c.u_k >= h_k
    U = normals(p, th); h = (H @ U.T).max(0)
    res = linprog([1, 0, 0], A_ub=-np.c_[np.ones(p), U], b_ub=-h, bounds=[(None, None)] * 3, method="highs")
    return res.fun, h

def inside_ok(H, p, th):
    r, h = r_of(H, p, th)
    U = normals(p, th); W = verts(p, th) * r; N0 = normals(p)
    A = np.r_[-U, np.tile(N0, (p, 1))]
    b = np.r_[r - h + 1e-12, (1 - (np.repeat(W, p, 0) * np.tile(N0, (p, 1))).sum(-1))]
    res = linprog([0, 0], A_ub=A, b_ub=b, bounds=[(None, None)] * 2, method="highs")
    return res.status == 0

def finite_trial(p, n, rng):
    X = sample(p, n, rng); H = X[ConvexHull(X).vertices] if n >= 3 else X
    f = lambda t: r_of(H, p, t)[0]
    span = np.pi / p if n < 100 else min(np.pi / p, 60.0 / n)
    grid = np.linspace(-span, span, 121 if n >= 100 else 241); vals = np.array([f(t) for t in grid])
    cands = []
    for i in range(len(grid)):   # every local minimum on the periodic grid, refined by golden section
        if vals[i] <= vals[max(i - 1, 0)] and vals[i] <= vals[min(i + 1, len(grid) - 1)]:
            a, b = grid[i] - (grid[1] - grid[0]), grid[i] + (grid[1] - grid[0])
            for _ in range(45):
                m1, m2 = a + 0.382 * (b - a), a + 0.618 * (b - a)
                if f(m1) < f(m2): b = m2
                else: a = m1
            th = (a + b) / 2; cands.append((f(th), th))
    best = min(c[0] for c in cands)
    opt = [th for v, th in cands if v <= best + 1e-9]
    return any(inside_ok(H, p, th) for th in opt), opt[0] * n

def limit_trial(p, rng, Dmax=12.0, mutant=False):
    L = 2 * math.tan(math.pi / p); U = normals(p); rows = []; rhs = []
    for k in range(p):
        m = rng.poisson(Dmax * L); D = rng.uniform(0, Dmax, m); s = rng.uniform(-L / 2, L / 2, m)
        for Di, si in zip(D, s):   # -(rho + C.u_k - Theta s_i) <= D_i
            rows.append([-1, si, -U[k, 0], -U[k, 1]]); rhs.append(Di)
    A = np.array(rows); b = np.array(rhs)
    res = linprog([1, 0, 0, 0], A_ub=A, b_ub=b, bounds=[(None, None)] * 4, method="highs")
    rho, Th = res.x[0], res.x[1]
    # among optima (fix rho, keep Theta's sign region): exists (Theta, C) with feasibility and inside condition
    ok = False
    for sg in (1, -1):
        A2 = np.r_[np.c_[A[:, 1:]], np.c_[(0 if mutant else sg * L / 2) * np.ones(p), U]]   # vars (Theta, Cx, Cy)
        b2 = np.r_[b + rho, -rho * np.ones(p)]
        bnd = [(0, None) if sg == 1 else (None, 0), (None, None), (None, None)]
        r2 = linprog([0, 0, 0], A_ub=A2, b_ub=b2 + 1e-9, bounds=bnd, method="highs")
        ok |= r2.status == 0
    return ok, Th

if __name__ == "__main__":
    mode = sys.argv[1]; rng = np.random.default_rng(int(sys.argv[-1]))
    res = []
    try:
        if mode == "finite":
            p, n, T = int(sys.argv[2]), int(sys.argv[3]), int(sys.argv[4])
            for _ in range(T): res.append(finite_trial(p, n, rng)[0])
        else:
            p, T = int(sys.argv[2]), int(sys.argv[3])
            Dm = float(sys.argv[5]) if len(sys.argv) > 6 else 12.0; mut = len(sys.argv) > 7
            for _ in range(T): res.append(limit_trial(p, rng, Dm, mut)[0])
    except Exception as e:
        print("stopped:", type(e).__name__)
    k = len(res); m = sum(res); print(f"{mode} p={sys.argv[2]} trials={k} P(inside)={m/k:.4f} +- {math.sqrt(m/k*(1-m/k)/k):.4f}")
