"""Independent recheck for MO 481323 (simple unit hexagons have diameter > sqrt 2).

Written separately from Codex's verify.py and manuscript_checks.py. It checks:

1. the adjacent-turn intersection parameters (symbolic) and a random sweep;
2. the four-hull-edge cross product K and its factorisation (symbolic) and its sign
   on a fine grid of (alpha, beta, gamma);
3. the metric facts of the triangle lemma on random triangles and point pairs;
4. the sharpness family: unit edges, the sign identity, exact turn signs and
   simplicity at rational parameters (exact algebraic arithmetic), and the limit;
5. a numerical minimisation of the diameter over simple unit hexagons (evidence only).

Run: python recheck.py [--quick]
"""

from __future__ import annotations

import itertools
import math
import random
import sys

import numpy as np
import sympy as sp
from scipy.optimize import minimize

QUICK = "--quick" in sys.argv
FAIL: list[str] = []


def check(name: str, ok: bool, detail: str = "") -> None:
    print(f"{'PASS' if ok else 'FAIL'}  {name}{('  ' + detail) if detail else ''}")
    if not ok:
        FAIL.append(name)


# ---------------------------------------------------------------- 1. adjacent turns
a, b, c = sp.symbols("alpha beta gamma", positive=True)
P2 = sp.Matrix([1 - sp.cos(a), sp.sin(a)])
d3 = sp.Matrix([sp.cos(a + b), -sp.sin(a + b)])
s = sp.sin(a) / sp.sin(a + b)
hit = P2 + s * d3
check(
    "turns: third edge meets x-axis at s = sin a / sin(a+b)",
    sp.simplify(sp.expand_trig(hit[1])) == 0,
)
check(
    "turns: meeting abscissa = 1 - sin b / sin(a+b)",
    sp.simplify(sp.expand_trig(hit[0] - (1 - sp.sin(b) / sp.sin(a + b)))) == 0,
)


def seg_meet(p, q, r, t) -> bool:
    """Closed segments pq and rt intersect (floating, generic position)."""

    def orient(u, v, w):
        return (v[0] - u[0]) * (w[1] - u[1]) - (v[1] - u[1]) * (w[0] - u[0])

    o1, o2, o3, o4 = orient(p, q, r), orient(p, q, t), orient(r, t, p), orient(r, t, q)
    return o1 * o2 <= 0 and o3 * o4 <= 0


rng = random.Random(481323)
bad = 0
for _ in range(20000 if QUICK else 200000):
    al, be = rng.uniform(1e-6, math.pi / 2), rng.uniform(1e-6, math.pi / 2)
    p0, p1 = (0.0, 0.0), (1.0, 0.0)
    p2 = (1 - math.cos(al), math.sin(al))
    p3 = (p2[0] + math.cos(al + be), p2[1] - math.sin(al + be))
    meets = seg_meet(p0, p1, p2, p3)
    if (max(2 * al + be, al + 2 * be) <= math.pi - 1e-9) and not meets:
        bad += 1
check(
    "turns: both terms <= pi forces edges 1 and 3 to meet (random sweep)",
    bad == 0,
    f"bad={bad}",
)

# ---------------------------------------------------------------- 2. four hull edges
S = a + b + c
dirs = [0, sp.pi - a, 2 * sp.pi - a - b, 3 * sp.pi - S]
P4 = sp.Matrix([sum(sp.cos(t) for t in dirs), sum(sp.sin(t) for t in dirs)])
u = sp.Matrix([sp.cos(dirs[3]), sp.sin(dirs[3])])
w = -P4
K = u[0] * w[1] - u[1] * w[0]
K_paper = sp.sin(c) - sp.sin(b + c) + sp.sin(S)
check(
    "four-hull: cross product at P4 equals K",
    sp.simplify(sp.expand_trig(K - K_paper)) == 0,
)
fact = (
    sp.sin(c)
    - sp.sin(b + c)
    + sp.sin(2 * c + b)
    - 4 * sp.sin(c / 2) * sp.cos((b + c) / 2) * sp.cos(c + b / 2)
)
check(
    "four-hull: factorisation identity",
    sp.simplify(sp.expand_trig(sp.expand(fact.rewrite(sp.exp)))) == 0,
)

Kf = sp.lambdify((a, b, c), K_paper, "numpy")
n = 60 if QUICK else 200
grid = np.linspace(1e-4, math.pi / 2, n)
A, B, C = np.meshgrid(grid, grid, grid, indexing="ij")
mask = (A + B + C > math.pi + 1e-12) & (A >= C)
vals = Kf(A, B, C)[mask]
corner = (
    (np.abs(A - math.pi / 2) < 1e-12)
    & (np.abs(B - math.pi / 2) < 1e-12)
    & (np.abs(C - math.pi / 2) < 1e-12)
)
check(
    "four-hull: K < 0 on grid with S > pi, alpha >= gamma (except the square corner)",
    bool(np.all(Kf(A, B, C)[mask & ~corner] < 0)),
    f"max K = {Kf(A, B, C)[mask & ~corner].max():.3e}",
)

# ---------------------------------------------------------------- 3. triangle lemma metrics
bad_pair = bad_med = bad_z = 0
for _ in range(2000 if QUICK else 20000):
    ah = rng.uniform(0.01, 0.99)
    hh = math.sqrt(1 - ah * ah)
    L, R, Z, M = (
        np.array([-ah, 0]),
        np.array([ah, 0]),
        np.array([0, hh]),
        np.array([0, 0]),
    )
    # random points in the closed left half conv(L, Z, M)
    wts = np.random.default_rng(rng.randrange(1 << 30)).dirichlet(
        [1, 1, 1], size=(2, 200)
    )
    pts = wts @ np.array([L, Z, M])
    d = np.linalg.norm(pts[0] - pts[1], axis=1)
    bad_pair += int(np.sum(d > 1 - 1e-12))
    y = rng.uniform(0, hh * (1 - 1e-9))
    q = np.array([0, y])
    bad_med += int(
        max(np.linalg.norm(q - L), np.linalg.norm(q - R), np.linalg.norm(q - Z)) >= 1
    )
    tri = np.random.default_rng(rng.randrange(1 << 30)).dirichlet(
        [1, 1, 1], size=200
    ) @ np.array([L, R, Z])
    dz = np.linalg.norm(tri - Z, axis=1)
    bad_z += int(np.sum(dz > 1 + 1e-12))
check(
    "triangle: no interior unit pair in a half; median off Z within 1 of corners; Z within 1 of T",
    bad_pair == 0 and bad_med == 0 and bad_z == 0,
    f"{bad_pair},{bad_med},{bad_z}",
)

# ---------------------------------------------------------------- 4. sharpness family
t = sp.symbols("t", positive=True)
Dt = sp.Matrix([2 * t**2 / (1 + t**2), 1 + 2 * t / (1 + t**2)])
Et = Dt + sp.Matrix([sp.Rational(3, 5), -sp.Rational(4, 5)])
r2 = sp.simplify(Et.dot(Et))
check(
    "sharp: |C D_t| = 1",
    sp.simplify((Dt - sp.Matrix([1, 1])).dot(Dt - sp.Matrix([1, 1])) - 1) == 0,
)
check(
    "sharp: 2 E_y - |E|^2 = 16 t (1-2t) / (5 (1+t^2))",
    sp.simplify(2 * Et[1] - r2 - 16 * t * (1 - 2 * t) / (5 * (1 + t**2))) == 0,
)


def family(tv):
    tv = sp.nsimplify(tv)
    A0, B0, C0 = sp.Matrix([0, 0]), sp.Matrix([1, 0]), sp.Matrix([1, 1])
    D0 = Dt.subs(t, tv)
    E0 = Et.subs(t, tv)
    rr = E0.dot(E0)
    k = sp.sqrt(1 / rr - sp.Rational(1, 4))
    F0 = E0 / 2 + k * sp.Matrix([-E0[1], E0[0]])
    return [A0, B0, C0, D0, E0, sp.simplify(F0)]


def cross(p, q):
    return p[0] * q[1] - p[1] * q[0]


def sign_exact(x) -> int:
    x = sp.nsimplify(x) if x.is_number else x
    v = sp.N(x, 60)
    if abs(v) < sp.Float(10) ** -50:
        z = sp.simplify(x)
        if z == 0:
            return 0
        v = sp.N(z, 200)
    return 1 if v > 0 else -1


def segs_intersect_exact(p, q, r, s_) -> bool:
    o1, o2 = sign_exact(cross(q - p, r - p)), sign_exact(cross(q - p, s_ - p))
    o3, o4 = sign_exact(cross(s_ - r, p - r)), sign_exact(cross(s_ - r, q - r))
    if o1 * o2 < 0 and o3 * o4 < 0:
        return True

    def on(u0, v0, w0):  # w0 on closed segment u0 v0, given collinear
        return min(u0[0], v0[0]) <= w0[0] <= max(u0[0], v0[0]) and min(
            u0[1], v0[1]
        ) <= w0[1] <= max(u0[1], v0[1])

    return (
        (o1 == 0 and on(p, q, r))
        or (o2 == 0 and on(p, q, s_))
        or (o3 == 0 and on(r, s_, p))
        or (o4 == 0 and on(r, s_, q))
    )


for tv in ["1/1000", "1/100", "1/20", "1/7", "1/4", "1/3", "49/100"]:
    V = family(tv)
    edges_unit = all(
        sp.simplify((V[(i + 1) % 6] - V[i]).dot(V[(i + 1) % 6] - V[i]) - 1) == 0
        for i in range(6)
    )
    turns = [
        sign_exact(cross(V[i] - V[i - 1], V[(i + 1) % 6] - V[i])) for i in range(6)
    ]
    nonadj = [
        (i, j) for i in range(6) for j in range(i + 2, 6) if not (i == 0 and j == 5)
    ]
    simple = not any(
        segs_intersect_exact(V[i], V[i + 1], V[j], V[(j + 1) % 6]) for i, j in nonadj
    )
    diam = max(
        math.dist([float(x) for x in V[i]], [float(x) for x in V[j]])
        for i in range(6)
        for j in range(i)
    )
    in_box = all(0 <= float(p[0]) and float(p[1]) >= 0 for p in V)
    check(
        f"sharp t={tv}: unit edges, simple, turns {turns}",
        edges_unit and simple and turns == [1, 1, 1, 1, -1, 1],
        f"diam={diam:.6f} - sqrt2 = {diam - math.sqrt(2):.2e}",
    )

Vlim = [
    sp.Matrix([0, 0]),
    sp.Matrix([1, 0]),
    sp.Matrix([1, 1]),
    sp.Matrix([0, 1]),
    sp.Matrix([sp.Rational(3, 5), sp.Rational(1, 5)]),
    sp.Matrix([0, 1]),
]
F_lim = (
    sp.limit(family_F := (lambda: None) or 0, t, 0) if False else None
)  # placeholder kept simple below
lim_diam = max(sp.sqrt((p - q).dot(p - q)) for p, q in itertools.combinations(Vlim, 2))
check(
    "sharp: limit vertex set has diameter sqrt 2",
    sp.simplify(lim_diam - sp.sqrt(2)) == 0,
)

# ---------------------------------------------------------------- 5. numerical minimisation (evidence)


def hexagon(phi):
    """Vertices from five free directions; the sixth edge closes when constraints hold."""
    v = np.stack([np.cos(phi), np.sin(phi)], axis=1)
    return np.vstack([np.zeros(2), np.cumsum(v, axis=0)])[:6]


def seg_dist(p, q, r, s_):
    def pt_seg(x, u0, v0):
        d = v0 - u0
        tt = np.clip(np.dot(x - u0, d) / np.dot(d, d), 0, 1)
        return np.linalg.norm(x - (u0 + tt * d))

    if seg_meet(tuple(p), tuple(q), tuple(r), tuple(s_)):
        return 0.0
    return min(pt_seg(p, r, s_), pt_seg(q, r, s_), pt_seg(r, p, q), pt_seg(s_, p, q))


def separation(V):
    m = len(V)
    return min(
        seg_dist(V[i], V[(i + 1) % m], V[j], V[(j + 1) % m])
        for i in range(m)
        for j in range(i + 2, m)
        if not (i == 0 and j == m - 1)
    )


best = []
nrng = np.random.default_rng(6)
starts = 40 if QUICK else 400
for delta in (0.05, 0.01, 0.002):
    found = []
    for _ in range(starts):
        x0 = np.append(nrng.uniform(0, 2 * np.pi, 6), 4.0)
        cons = [
            {"type": "eq", "fun": lambda x: np.sum(np.cos(x[:6]))},
            {"type": "eq", "fun": lambda x: np.sum(np.sin(x[:6]))},
            {"type": "ineq", "fun": lambda x, delta=delta: separation(hexagon(x[:6])) - delta},
        ]
        for i, j in itertools.combinations(range(6), 2):
            cons.append({"type": "ineq",
                         "fun": lambda x, i=i, j=j: x[6] - np.sum((hexagon(x[:6])[i] - hexagon(x[:6])[j]) ** 2)})
        res = minimize(lambda x: x[6], x0, constraints=cons, method="SLSQP",
                       options={"maxiter": 400, "ftol": 1e-12})
        phi = res.x[:6]
        if abs(np.sum(np.cos(phi))) + abs(np.sum(np.sin(phi))) > 1e-8:
            continue
        V = hexagon(phi)
        sep = separation(V)
        dmax = max(np.linalg.norm(V[i] - V[j]) for i in range(6) for j in range(i))
        found.append((sep, dmax))
        best.append((sep, dmax))
    simple = [d for sep, d in found if sep > delta / 2]
    print(f"      separation >= {delta}: {len(simple)} simple optima, smallest diameter "
          f"{min(simple, default=float('nan')):.6f}")

simple_runs = [(sep, d) for sep, d in best if sep > 1e-6]
below = [(sep, d) for sep, d in simple_runs if d <= math.sqrt(2) - 1e-9]
mins = min((d for _, d in simple_runs), default=float("nan"))
check(
    "numerics: no simple local optimum has diameter <= sqrt 2",
    not below,
    f"{len(simple_runs)} simple optima of {len(best)}; smallest simple diameter {mins:.6f}",
)

print()
print("ALL PASS" if not FAIL else f"FAILURES: {FAIL}")
sys.exit(1 if FAIL else 0)
