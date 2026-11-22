"""Independent check (A): eta = det(x, gradF(W), gradG(W)) / prod L, W = x cross dx,
pulls back to a regular section of S^4 Omega_Y on the resolved Kummer cover Y of P^2.

Written from the statement of dzoba E1 section 6.3 only; uses none of their code.
Coordinates: x = (e,u,v) on P^2, cell lines L_ab = e + a u + b v, (a,b) in {-1,0,1}^2.
"""
from __future__ import annotations

import itertools

import sys

import sympy as S

e, u, v = S.symbols("e u v")
l0, l1, l2 = S.symbols("l0 l1 l2")
p, y, dp, dy = S.symbols("p y dp dy")
X, w, dX, dw = S.symbols("X w dX dw")

F = l1**3 - l0**2 * l1
G = l2**3 - l0**2 * l2
CELLS = [(a, b) for a in (-1, 0, 1) for b in (-1, 0, 1)]


def L(x, ab):
    a, b = ab
    return x[0] + a * x[1] + b * x[2]


def eta_parts(x, dx):
    """Numerator Q(x, W) and denominator prod L for a lift x and its differential dx."""
    W = x.cross(dx)
    sub = dict(zip((l0, l1, l2), W))
    gF = S.Matrix([S.diff(F, s) for s in (l0, l1, l2)]).subs(sub)
    gG = S.Matrix([S.diff(G, s) for s in (l0, l1, l2)]).subs(sub)
    Q = S.Matrix.hstack(x, gF, gG).det()
    den = S.prod([L(x, ab) for ab in CELLS])
    return S.expand(Q), S.expand(den)


def frame(rows):
    """Affine chart: lift x = M^{-1} (1, p, y) with M rows = the given linear forms."""
    M = S.Matrix([[r.coeff(s) for s in (e, u, v)] for r in rows])
    assert M.det() != 0
    Mi = M.inv()
    return Mi * S.Matrix([1, p, y]), Mi * S.Matrix([0, dp, dy])


def check_line(ab):
    a, b = ab
    Lk = e + a * u + b * v
    # Generic auxiliary forms so that the chart is valid along most of the line.
    x, dx = frame([3 * e + 5 * u + 7 * v + 2 * Lk, 11 * e - 13 * u + 17 * v, Lk])
    Q, den = eta_parts(x, dx)
    # den contains y exactly once (from L_k); the other eight factors are units at a general point of y = 0.
    assert S.Poly(den, y).as_expr().subs(y, 0) == 0
    assert S.Poly(S.cancel(den / y), y).as_expr().subs(y, 0) != 0
    PQ = S.Poly(Q, dp, dy)
    bad = []
    # On z^2 = y: dy = 2 z dz, 1/y = 1/z^2. dp^i dy^j term needs j >= 2 or coefficient divisible by y.
    for (i, j), c in PQ.terms():
        if j < 2 and S.expand(c.subs(y, 0)) != 0:
            bad.append((i, j))
    return bad


def triple_points():
    out = []
    for A, B, C in itertools.combinations(CELLS, 3):
        M = S.Matrix([[1, *A], [1, *B], [1, *C]])
        if M.det() == 0:
            out.append((A, B, C))
    return out


def check_triple(A, B, C):
    LA, LB, LC = (e + a * u + b * v for a, b in (A, B, C))
    al, be = S.symbols("al be")
    sol = S.solve(S.Poly(LC - al * LA - be * LB, e, u, v).coeffs(), [al, be], dict=True)
    assert len(sol) == 1
    al_, be_ = sol[0][al], sol[0][be]
    assert al_ != 0 and be_ != 0
    H = 2 * e + 3 * u + 5 * v  # not through the triple point (checked below)
    x, dx = frame([H, al_ * LA, be_ * LB])
    P = S.Matrix([[1, *A], [1, *B]]).nullspace()  # not needed; point check via solve
    pt = S.solve([LA, LB], [u, v], dict=True)[0]
    assert S.simplify(H.subs(pt).subs(e, 1)) != 0
    # Now p = alpha L_A / H, y = beta L_B / H, p + y = L_C / H.
    assert S.simplify((x[0] + al_ * 0) * 0) == 0
    Q, den = eta_parts(x, dx)
    # Resolution chart of the A1 node: p = X^2 (w^2-1)^2 / 4, y = X^2 w^2.
    ps = X**2 * (w**2 - 1) ** 2 / 4
    ys = X**2 * w**2
    dps = S.diff(ps, X) * dX + S.diff(ps, w) * dw
    dys = S.diff(ys, X) * dX + S.diff(ys, w) * dw
    sub = {p: ps, y: ys, dp: dps, dy: dys}
    num = S.expand(Q.subs(sub))
    dd = S.expand(den.subs({p: ps, y: ys}))
    worst = None
    for (i, j), c in S.Poly(num, dX, dw).terms():
        r = S.factor(S.cancel(c / dd))
        n_, d_ = S.fraction(r)
        d0 = S.expand(d_.subs(X, 0))
        # Regular near the exceptional curve iff the reduced denominator is a unit along X = 0.
        ok = d0 != 0 and S.Poly(d0, w).degree() == 0
        if not ok:
            worst = (i, j, S.factor(d_))
            break
    return worst


def main():
    bad = 0
    print("cell-line conditions:")
    for ab in CELLS:
        res = check_line(ab)
        bad += bool(res)
        print("  L", ab, "OK" if not res else f"FAIL {res}")
    tps = triple_points()
    print("triple points:", len(tps))
    assert len(tps) == 8, len(tps)
    for t in tps:
        res = check_triple(*t)
        bad += res is not None
        print("  ", t, "OK" if res is None else f"FAIL {res}")
    if bad:
        sys.exit(f"FAIL: eta is not regular at {bad} of the 9 lines and 8 triple points")
    print("eta regular along all 9 cell lines and at all 8 triple points")


if __name__ == "__main__":
    main()
