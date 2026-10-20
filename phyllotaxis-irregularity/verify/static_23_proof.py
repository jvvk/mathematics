"""Exact first-order analysis of the first disk placed on a near-lattice (2,3) front with a 60-degree notch.

Front (left to right): disks z0 = Z, z1 = A, z2 = B, z3 = C, z4 = E, front vectors D1, D2, U1, U2, U3
(D1 = A - Z, D2 = B - A, U1 = C - B, U2 = E - C, U3 = Z + Lambda - E). Deviations from the lattice:
  hinge at A   h(D1, D2) = 180 + alpha
  notch at B   h(D2, U1) =  60 + sigma
  hinge at C   h(U1, U2) = 180 - eps
  hinge at E   h(U2, U3) = 180 - zeta
and the rate c, with every disk (seeds included) of diameter d = 1 + c*Im z, consecutive disks touching.
At p = (alpha, sigma, eps, zeta, c) = 0 this is the rhombic lattice with tan(beta_D) = -3 sqrt3 and
up vectors at beta_D + 120 degrees (paper, notch-60 lattice law).

Step 1 (exact, p = 0): every candidate pair of front disks (all disk images on the cylinder), its apex,
its validity, its height. The lowest valid apex Q0 is shared by several pairs: Q0 touches four disks.
Step 2 (first order): near Q0 the free region is {x : n_k . x >= s_k(p)} for the touching disks k, with
n_k = Q0 - z_k and s_k linear in p. The new disk is the lowest point of that polygon; it is a pentagon
exactly when the lowest vertex is the one touching A and E. Prints the exact linear forms that decide it.
Step 3: checks the prediction against the independent simulator with consistent seeds.
"""

from __future__ import annotations

import itertools
import math
import os
import sys

import sympy as sp

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from independent_stack import Stack

al, si, ep, ze, c = sp.symbols("alpha sigma epsilon zeta c", real=True)
P = (al, si, ep, ze, c)
NAMES = ["Z", "A", "B", "C", "E"]

# ---------- zeroth order: exact lattice ----------
cD, sD = (
    1 / sp.sqrt(28),
    -3 * sp.sqrt(3) / sp.sqrt(28),
)  # cos, sin of beta_D, tan = -3 sqrt3
D0 = sp.Matrix([cD, sD])
R120 = sp.Matrix(
    [[sp.Rational(-1, 2), -sp.sqrt(3) / 2], [sp.sqrt(3) / 2, sp.Rational(-1, 2)]]
)
U0 = sp.simplify(R120 * D0)
assert (
    sp.simplify(2 * D0[1] + 3 * U0[1]) == 0
)  # closure: the front is periodic horizontally
vec0 = [D0, D0, U0, U0, U0]
z0 = [sp.Matrix([0, 0])]
for v in vec0[:-1]:
    z0.append(sp.simplify(z0[-1] + v))
LAM = sp.simplify(sum(v[0] for v in vec0))
assert sp.simplify(LAM - sp.sqrt(7)) == 0, LAM  # circumference sqrt7


def J(v: sp.Matrix) -> sp.Matrix:
    """Rotation by +90 degrees."""
    return sp.Matrix([-v[1], v[0]])


def apex0(p: sp.Matrix, q: sp.Matrix):
    """Unit-distance apex above the segment p -> q (unit diameters), or None if |pq| > 2."""
    d = q - p
    L2 = sp.simplify(d.dot(d))
    if L2 > 4:
        return None
    h = sp.sqrt(1 - L2 / 4)
    return sp.simplify((p + q) / 2 + h * J(d) / sp.sqrt(L2))


# every disk image near the front: index k, shift s (in units of LAM)
images = [(k, s) for k in range(5) for s in (-1, 0, 1)]


def pos0(k: int, s: int) -> sp.Matrix:
    return z0[k] + sp.Matrix([s * LAM, 0])


cands = []
for a in range(5):
    for gap in range(4):  # b = a + gap + 1, cyclically; gap = 0 T, 1 R, 2 P, 3 "-2"
        b, s = (a + gap + 1) % 5, (1 if a + gap + 1 >= 5 else 0)
        Q = apex0(pos0(a, 0), pos0(b, s))
        if Q is None:
            continue
        clear = min(
            sp.sqrt(((Q - pos0(k, t)).T * (Q - pos0(k, t)))[0])
            for k, t in images
            if (k, t) not in ((a, 0), (b, s))
        )
        cands.append((sp.nsimplify(Q[1]), a, b, s, gap, sp.simplify(clear - 1), Q))

def above_front(Q: sp.Matrix) -> bool:
    """The new disk lies above the front polyline (the stack fills the region below it)."""
    xs = [float(pos0(k, t)[0]) for k, t in images]
    pts = sorted((float(pos0(k, t)[0]), float(pos0(k, t)[1])) for k, t in images)
    x = float(Q[0])
    for (x1, y1), (x2, y2) in zip(pts, pts[1:]):
        if x1 <= x <= x2:
            return float(Q[1]) > y1 + (y2 - y1) * (x - x1) / (x2 - x1)
    raise ValueError(xs)


valid = [x for x in cands if x[5] >= 0 and above_front(x[6])]
ymin = min(x[0] for x in valid)
print("Step 1: candidates at the lattice (height, pair, gap, clearance-1):")
for y, a, b, s, gap, cl, Q in sorted(cands, key=lambda t: float(t[0])):
    tag = ("valid" if above_front(Q) else "below front") if cl >= 0 else "overlaps"
    print(
        f"  y={float(y):+.5f}  {NAMES[a]}-{NAMES[b]}{'+' if s else ''}  gap {gap}  clear-1 = {float(cl):+.5f}  {tag}"
    )
ties = [x for x in valid if sp.simplify(x[0] - ymin) == 0]
Q0 = ties[0][6]
assert all(sp.simplify(t[6] - Q0) == sp.zeros(2, 1) for t in ties)
nxt = min(float(x[0]) for x in valid if sp.simplify(x[0] - ymin) != 0)
print(
    f"lowest valid height {float(ymin):+.5f} = {sp.nsimplify(ymin)}, shared by {len(ties)} pairs; next valid {nxt:+.5f}"
)
touch = [
    (k, t)
    for k, t in images
    if sp.simplify((Q0 - pos0(k, t)).dot(Q0 - pos0(k, t)) - 1) == 0
]
print("Q0 touches", [NAMES[k] + ("+" if t else "") for k, t in touch])
assert sorted(NAMES[k] for k, _ in touch) == ["A", "C", "E", "Z"]

# ---------- first order ----------
# bearings: theta_k = theta_k0 + phi + r_k ; lengths L_k = 1 + c (y_k + y_{k+1}) / 2 (seeds consistent)
r = [al, 0, -si, -si + ep, -si + ze]
yk = [z[1] for z in z0] + [z0[0][1]]
L1 = [c * (yk[k] + yk[k + 1]) / 2 for k in range(5)]  # first-order part of the length
phi = sp.Symbol("phi")
# closure Im(sum L_k e^{i theta_k}) = 0, first order
clos = sum(L1[k] * vec0[k][1] + (phi + r[k]) * vec0[k][0] for k in range(5))
phi_s = sp.solve(sp.expand(clos), phi)[0]
dvec = [sp.expand(L1[k] * vec0[k] + (phi_s + r[k]) * J(vec0[k])) for k in range(5)]
dz = [sp.zeros(2, 1)]
for k in range(4):
    dz.append(sp.expand(dz[-1] + dvec[k]))
dLAM = sp.expand(sum(dvec[k][0] for k in range(5)))
Y0 = Q0[1]


def shift(k: int, t: int) -> sp.Expr:
    """s_k: the free region near Q0 is n_k . x >= s_k, with x the first-order displacement of the new disk."""
    n = Q0 - pos0(k, t)
    dzk = dz[k] + sp.Matrix([t * dLAM, 0])
    return sp.expand(n.dot(dzk) + c * (yk[k] + Y0) / 2)


cons = {NAMES[k]: (Q0 - pos0(k, t), shift(k, t)) for k, t in touch}
for nm, (n, s) in cons.items():
    print(
        f"  {nm}: normal ({sp.nsimplify(n[0])}, {sp.nsimplify(n[1])}), s = {sp.nsimplify(s)}"
    )


def vertex(i: str, j: str) -> sp.Matrix:
    (n1, s1), (n2, s2) = cons[i], cons[j]
    M = sp.Matrix([[n1[0], n1[1]], [n2[0], n2[1]]])
    return sp.simplify(M.inv() * sp.Matrix([s1, s2]))


def slack(x: sp.Matrix, k: str) -> sp.Expr:
    n, s = cons[k]
    return sp.nsimplify(sp.expand(n.dot(x) - s))


pairs = list(itertools.combinations(cons, 2))
V = {
    pr: vertex(*pr)
    for pr in pairs
    if sp.Matrix([cons[pr[0]][0].T, cons[pr[1]][0].T]).det() != 0
}
print("\nStep 2: vertices of the local free polygon (first order):")
for pr, x in V.items():
    print(
        f"  {pr[0]}{pr[1]}: height {sp.nsimplify(sp.expand(x[1]))};  slacks "
        + ", ".join(f"{k}: {slack(x, k)}" for k in cons if k not in pr)
    )

# the pentagon: vertex A-E feasible (slack to Z and C positive) and lowest among feasible vertices
xP = V[("A", "E")]
fP = {k: slack(xP, k) for k in ("Z", "C")}
print(
    "\nPentagon vertex A-E is feasible iff",
    " and ".join(f"{v} > 0" for v in fP.values()),
)
# width of the Z-E channel: Z and E have opposite normals, so a free point exists iff s_Z + s_E <= 0
assert sp.simplify(cons["Z"][0] + cons["E"][0]) == sp.zeros(2, 1)
gapZE = sp.nsimplify(-(cons["Z"][1] + cons["E"][1]))
print("Z-E channel open iff", gapZE, "> 0")

# ---------- Step 3: simulator with consistent seeds ----------
num = {k: float(v) for k, v in zip(("cD", "sD"), (cD, sD))}
bD0 = math.atan2(num["sD"], num["cD"])


def build(alpha, sigma, eps, zeta, cc):
    """Exact front with consistent seeds: solve global rotation phi and heights by fixed point."""
    th_rel = [
        alpha,
        0.0,
        2 * math.pi / 3 - sigma,
        2 * math.pi / 3 - sigma + eps,
        2 * math.pi / 3 - sigma + zeta,
    ]
    phi_ = 0.0
    ys = [0.0] * 5
    for _ in range(200):
        # lengths from current heights
        Ls = [1 + cc * (ys[k] + ys[(k + 1) % 5]) / 2 for k in range(5)]
        # solve closure for phi by Newton
        for _ in range(50):
            f = sum(Ls[k] * math.sin(bD0 + phi_ + th_rel[k]) for k in range(5))
            g = sum(Ls[k] * math.cos(bD0 + phi_ + th_rel[k]) for k in range(5))
            phi_ -= f / g
        pts = [(0.0, 0.0)]
        for k in range(4):
            a = bD0 + phi_ + th_rel[k]
            pts.append(
                (pts[-1][0] + Ls[k] * math.cos(a), pts[-1][1] + Ls[k] * math.sin(a))
            )
        ys = [p[1] for p in pts]
    lam = sum(Ls[k] * math.cos(bD0 + phi_ + th_rel[k]) for k in range(5))
    return [(x / lam, y / lam, (1 + cc * y) / lam) for x, y in pts], 1 / lam, cc


def first_event(alpha, sigma, eps, zeta, cc):
    pts, b0, cc = build(alpha, sigma, eps, zeta, cc)
    S = Stack(pts, b0, cc, tol=1e-13)
    p0 = S.parastichy()
    dl = S.step()
    return {1: "T", 0: "R", -1: "P"}.get(dl, f"X{dl}"), p0, S.parastichy()


def predict(alpha, sigma, eps, zeta, cc):
    sub = {al: alpha, si: sigma, ep: eps, ze: zeta, c: cc}
    if float(gapZE.subs(sub)) < 0:
        return "jam"
    feas = {
        pr: x
        for pr, x in V.items()
        if all(float(slack(x, k).subs(sub)) >= 0 for k in cons if k not in pr)
    }
    low = min(feas, key=lambda pr: float(V[pr][1].subs(sub)))
    return {("A", "E"): "P", ("A", "C"): "R"}.get(low, "".join(low))


if __name__ == "__main__":
    print(
        "\nStep 3: prediction vs simulator (alpha, sigma, eps, zeta, c) -> predicted / simulated"
    )
    t = 2e-3
    tests = [
        (0, 0.9 * t, t, t / 2, 0),
        (0, 0.7 * t, t, t / 2, 0),
        (0, 0.55 * t, t, t / 2, 0),
        (0, 0.45 * t, t, 0, 0),
        (0, 1.1 * t, t, t / 2, 0),
        (0.3 * t, 0.8 * t, t, 0.2 * t, 0),
        (-0.3 * t, 0.8 * t, t, 0.2 * t, 0),
        (0.2 * t, 0.75 * t, t, 0.5 * t, -0.2 * t),
        (0.2 * t, 0.75 * t, t, 0.5 * t, -0.5 * t),
        (0, 0.75 * t, t, 0.5 * t, -t),
        (0, 0.75 * t, t, 0.5 * t, -2 * t),
        (0.1 * t, 0.8 * t, t, -0.4 * t, -0.3 * t),
    ]
    bad = 0
    from static_channel import valid as front_valid

    skipped = 0
    for p in tests:
        pts, b0, cc = build(*p)
        if not front_valid([(x / b0, y / b0, d / b0) for x, y, d in pts], 1 / b0):
            skipped += 1
            print(f"  {tuple(round(v / t, 2) for v in p)} x {t}: invalid front (two disks overlap), skipped")
            continue
        pr, (ev, a, b) = predict(*p), first_event(*p)
        ok = (pr == ev) or (pr == "jam" and ev == "T")
        bad += not ok
        print(
            f"  {tuple(round(v / t, 2) for v in p)} x {t}: predicted {pr}, simulated {ev} {a}->{b}  {'ok' if ok else 'MISMATCH'}"
        )
    print("mismatches:", bad, " invalid fronts skipped:", skipped)


# ---------- Step 4: the linear forms against exact nonlinear geometry ----------
def exact_slacks(alpha, sigma, eps, zeta, cc):
    """Exact apex touching A and E (diameter law included), and its slacks to Z and C, in lattice units."""
    pts, b0, cc = build(alpha, sigma, eps, zeta, cc)
    lam = 1 / b0
    Z, A, C, E = [(pts[k][0] * lam, pts[k][1] * lam, pts[k][2] * lam) for k in (0, 1, 3, 4)]
    S = Stack([], 1.0, cc)
    q = S.apex(A, E)
    sl = {nm: math.hypot(q[0] - w[0], q[1] - w[1]) - (q[2] + w[2]) / 2 for nm, w in (("Z", Z), ("C", C))}
    return sl, q[1]


if __name__ == "__main__":
    import random

    random.seed(1)
    fz = {k: sp.lambdify(P, slack(V[("A", "E")], k)) for k in ("Z", "C")}
    worst = 0.0
    for _ in range(6):
        d = [random.uniform(-1, 1) for _ in range(5)]
        for h in (1e-3, 1e-4):
            p = [h * v for v in d]
            sl, _ = exact_slacks(*p)
            for k in ("Z", "C"):
                lin = fz[k](*p)
                worst = max(worst, abs(sl[k] - lin) / h)
        print(f"  direction {[round(v, 2) for v in d]}: (exact - linear)/h at h=1e-4 -> "
              + ", ".join(f"{k} {(exact_slacks(*[1e-4 * v for v in d])[0][k] - fz[k](*[1e-4 * v for v in d])) / 1e-4:+.2e}" for k in ("Z", "C")))
    assert worst < 5e-3, worst
    print("Step 4: linear forms agree with the exact slacks to first order (max |exact-linear|/h =", f"{worst:.1e})")
