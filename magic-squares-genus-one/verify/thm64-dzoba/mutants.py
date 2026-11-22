"""Mutation tests: the line and node checks in eta_regular.py must reject wrong forms.

M0 eta itself: passes (control).
M1 a random Q (linear in x, quartic in l): must fail lines and nodes.
M2 eta * H / L_A (extra pole on one cell line): must fail that line and its triple points.
M3 a form satisfying the line conditions on 8 cell lines only. Planned as a mutant; on rerun the 8-line space
   equals the 9-line space (dimension 11), so it plants nothing and is asserted as that finding (a control).
Also: the reflexive space modulo trivial forms (l.x) K(l) is 1-dimensional and equals eta.
"""
from __future__ import annotations

import random

import sympy as S

import eta_regular as R
from eta_space import C, MONS, Qgen, eta_Q, solve_space
from eta_regular import CELLS, L, X, dp, dw, dX, dy, e, frame, p, triple_points, u, v, w, y

H0 = 2 * e + 3 * u + 5 * v


def line_bad(Qf, k, mult=1):
    a, b = k
    Lk = e + a * u + b * v
    x, dx = frame([3 * e + 5 * u + 7 * v + 2 * Lk, 11 * e - 13 * u + 17 * v, Lk])
    num = S.expand(Qf(x, x.cross(dx)) * mult(x) if callable(mult) else Qf(x, x.cross(dx)))
    den = S.expand(S.prod([L(x, ab) for ab in CELLS]))
    # order of pole along y after the multiplier
    r = S.cancel(num / den)
    n_, d_ = S.fraction(S.together(r))
    kden = 0
    dpoly = S.Poly(d_, y)
    while S.expand(dpoly.as_expr().subs(y, 0)) == 0:
        dpoly = S.Poly(S.quo(dpoly.as_expr(), y, y), y); kden += 1
    for (i, j), c in S.Poly(S.expand(n_), dp, dy).terms():
        kn = 0
        cc = S.Poly(c, y)
        while not cc.is_zero and S.expand(cc.as_expr().subs(y, 0)) == 0:
            cc = S.Poly(S.quo(cc.as_expr(), y, y), y); kn += 1
        # on z^2 = y: z^(2 kn + j - 2 kden) must be >= 0
        if not cc.is_zero and 2 * kn + j - 2 * kden < 0:
            return True
    return False


def node_bad(Qf, tp, mult=None):
    A, B, Cc = tp
    LA, LB, LC = (e + a * u + b * v for a, b in tp)
    al, be = S.symbols("al be")
    sol = S.solve(S.Poly(LC - al * LA - be * LB, e, u, v).coeffs(), [al, be], dict=True)[0]
    x, dx = frame([H0, sol[al] * LA, sol[be] * LB])
    ps, ys = X**2 * (w**2 - 1) ** 2 / 4, X**2 * w**2
    sub = {p: ps, y: ys, dp: S.diff(ps, X) * dX + S.diff(ps, w) * dw, dy: S.diff(ys, X) * dX + S.diff(ys, w) * dw}
    num = Qf(x, x.cross(dx))
    if mult is not None:
        num = num * mult(x)
    num = S.expand(S.together(num).subs(sub))
    den = S.expand(S.prod([L(x, ab) for ab in CELLS]).subs({p: ps, y: ys}))
    n_, d_ = S.fraction(S.together(num / den))
    n_ = S.expand(n_); d_ = S.expand(d_)
    ordd = min(m[0] for m in S.Poly(d_, X).monoms())
    for _, c in S.Poly(n_, dX, dw).terms():
        ordn = min(m[0] for m in S.Poly(c, X).monoms())
        if ordn < ordd:
            return True
    return False


def report(name, Qf, mult=None):
    lb = [k for k in CELLS if line_bad(Qf, k, mult if mult else 1)]
    nb = [t for t in triple_points() if node_bad(Qf, t, mult)]
    print(f"{name}: line failures {lb}; node failures {len(nb)} {nb}")
    return lb, nb


def main():
    random.seed(1)
    tps = triple_points()
    assert report("M0 eta", eta_Q) == ([], []), "control: eta must pass"
    vec = [random.randint(-5, 5) for _ in C]
    lb, nb = report("M1 random", lambda x, W: Qgen(x, W).subs(dict(zip(C, vec))))
    assert len(lb) == 9 and len(nb) == 8, "M1: a random form must fail every line and node"
    LA = lambda x: x[0] + x[1] + x[2]
    lb, nb = report("M2 eta*H/L_(1,1)", eta_Q, mult=lambda x: (2 * x[0] + 3 * x[1] + 5 * x[2]) / LA(x))
    assert lb == [(1, 1)] and sorted(nb) == sorted(t for t in tps if (1, 1) in t), "M2: exactly line (1,1)"
    # M3: line conditions on the 8 lines other than (1,1).
    from eta_space import line_eqs
    saved = R.CELLS
    eqs = []
    for k in CELLS:
        if k == (1, 1):
            continue
        a, b = k
        Lk = e + a * u + b * v
        x, dx = frame([3 * e + 5 * u + 7 * v + 2 * Lk, 11 * e - 13 * u + 17 * v, Lk])
        Q = S.expand(Qgen(x, x.cross(dx)))
        for (i, j), c in S.Poly(Q, dp, dy).terms():
            if j < 2:
                eqs += S.Poly(S.expand(c.subs(y, 0)), p).coeffs()
    sp = solve_space(eqs)
    # pick a random element, discard trivial and eta directions implicitly: test it
    vec = sum((random.randint(-3, 3) * s for s in sp), S.zeros(len(C), 1))
    lb, nb = report(f"M3 8-line form (space dim {len(sp)})", lambda x, W: Qgen(x, W).subs(dict(zip(C, vec))))
    # Found on rerun: the conditions on the other 8 lines already imply the ninth, so M3 plants nothing.
    assert len(sp) == 11 and (lb, nb) == ([], []), "M3: the 8-line space should equal the 9-line space"
    # Effective reflexive dimension: quotient by trivial forms (l.x) K(l).
    full = solve_space(line_eqs(Qgen))
    xs = S.Matrix([e, u, v]); W = S.Matrix(S.symbols("W0:3"))
    forms = [S.expand(Qgen(xs, xs.cross(S.Matrix(S.symbols("d0:3")))).subs(dict(zip(C, s)))) for s in full]
    d = S.symbols("d0:3")
    rows = [S.Poly(f, e, u, v, *d).coeffs() for f in forms]
    allm = set()
    polys = [S.Poly(f, e, u, v, *d) for f in forms]
    for P_ in polys:
        allm |= set(P_.monoms())
    allm = sorted(allm)
    M = S.Matrix([[P_.coeff_monomial(m) for m in allm] for P_ in polys])
    print("reflexive dim:", len(full), " rank as actual differentials:", M.rank())
    assert len(full) == 11 and M.rank() == 1, "reflexive space: dimension 11, rank 1 as differentials"
    print("all expected outcomes hold")


if __name__ == "__main__":
    main()
