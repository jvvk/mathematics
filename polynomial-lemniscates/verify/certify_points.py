"""Certified lower bounds for the two sharp examples (Krawczyk test in interval arithmetic).

Example (2,2): P1 = z^2 - 1, P2 = (z - 1)^2 - 1 (Bernoulli lemniscates with foci +-1 and 0, 2), levels 1.
Example (2,3): P1 = (z - 1/10)^2 - 1, P2 = z^3/8000 - 1, levels 1.
Each intersection point z = x + iy solves the real system |P1|^2 - 1 = 0, |P2|^2 - 1 = 0.
Floating Newton finds approximate solutions; for each, a box X around it is certified to contain
exactly one solution by the Krawczyk test K(X) in int(X), with all arithmetic in mpmath intervals.
Pairwise disjoint certified boxes give a rigorous lower bound on the number of points.

    python3 certify_points.py
"""
from __future__ import annotations

import itertools

import mpmath as mp
from mpmath import iv

mp.mp.dps = 50
iv.dps = 50


def real_system(P):
    """F(x, y) = (|P(x+iy)|^2 - 1, ...) for a polynomial P given by complex coefficients (high first)."""
    return P


def poly_eval(coeffs, z):
    acc = 0
    for c in coeffs:
        acc = acc * z + c
    return acc


def F(c1, c2, x, y, ctx):
    """Real and imaginary parts handled by hand so that the same code runs for mp and iv."""
    def cmul(a, b):
        return (a[0] * b[0] - a[1] * b[1], a[0] * b[1] + a[1] * b[0])

    def ev(coeffs):
        acc = (ctx.mpf(0), ctx.mpf(0))
        for (re, im) in coeffs:
            acc = cmul(acc, (x, y))
            acc = (acc[0] + re, acc[1] + im)
        return acc
    p, q = ev(c1), ev(c2)
    return [p[0] ** 2 + p[1] ** 2 - 1, q[0] ** 2 + q[1] ** 2 - 1]


def jac(c1, c2, x, y, ctx):
    """Jacobian of F by exact differentiation: d|P|^2 = 2 Re(conj(P) P' dz)."""
    def cmul(a, b):
        return (a[0] * b[0] - a[1] * b[1], a[0] * b[1] + a[1] * b[0])

    def ev_and_der(coeffs):
        acc = (ctx.mpf(0), ctx.mpf(0))
        der = (ctx.mpf(0), ctx.mpf(0))
        for (re, im) in coeffs:
            der = cmul(der, (x, y))
            der = (der[0] + acc[0], der[1] + acc[1])
            acc = cmul(acc, (x, y))
            acc = (acc[0] + re, acc[1] + im)
        return acc, der
    rows = []
    for c in (c1, c2):
        p, d = ev_and_der(c)
        w = cmul((p[0], -p[1]), d)  # conj(P) P'
        # d/dx |P|^2 = 2 Re(conj P P'), d/dy = 2 Re(conj P P' i) = -2 Im(conj P P')
        rows.append([2 * w[0], -2 * w[1]])
    return rows


def newton(c1, c2, x, y):
    for _ in range(100):
        f = F(c1, c2, x, y, mp)
        J = mp.matrix(jac(c1, c2, x, y, mp))
        d = mp.lu_solve(J, -mp.matrix(f))
        x, y = x + d[0], y + d[1]
        if mp.norm(d) < mp.mpf(10) ** -40:
            break
    return x, y


def krawczyk(c1, c2, x0, y0, r):
    X = [iv.mpf([x0 - r, x0 + r]), iv.mpf([y0 - r, y0 + r])]
    Y = mp.inverse(mp.matrix(jac(c1, c2, x0, y0, mp)))
    fx = F(c1, c2, iv.mpf(x0), iv.mpf(y0), iv)
    JX = jac(c1, c2, X[0], X[1], iv)
    K = []
    for i in range(2):
        s = iv.mpf(x0 if i == 0 else y0)
        s -= sum(iv.mpf(Y[i, k]) * fx[k] for k in range(2))
        for j in range(2):
            m = (1 if i == j else 0) - sum(iv.mpf(Y[i, k]) * JX[k][j] for k in range(2))
            s += m * (X[j] - iv.mpf(x0 if j == 0 else y0))
        K.append(s)
    inside = all(K[i].a > X[i].a and K[i].b < X[i].b for i in range(2))
    return inside, X


def certify(name, c1, c2, R, grid):
    approx = []
    for gx, gy in itertools.product(mp.linspace(-R, R, grid), repeat=2):
        try:
            x, y = newton(c1, c2, mp.mpf(gx), mp.mpf(gy))
        except ZeroDivisionError:
            continue
        f = F(c1, c2, x, y, mp)
        if max(abs(f[0]), abs(f[1])) < mp.mpf(10) ** -35 and all(
                abs(x - a) + abs(y - b) > mp.mpf(10) ** -10 for a, b in approx):
            approx.append((x, y))
    r = mp.mpf(10) ** -20
    boxes = []
    for x, y in approx:
        ok, X = krawczyk(c1, c2, x, y, r)
        assert ok, f"Krawczyk failed at {x}, {y}"
        boxes.append(X)
    for A, B in itertools.combinations(boxes, 2):
        assert A[0].b < B[0].a or B[0].b < A[0].a or A[1].b < B[1].a or B[1].b < A[1].a
    print(f"{name}: {len(boxes)} pairwise disjoint certified points")
    for x, y in sorted(approx):
        print(f"  {mp.nstr(x, 15):>20} {mp.nstr(y, 15):>20}")
    return len(boxes)


if __name__ == "__main__":
    q = mp.mpf(1) / 10
    # coefficients (re, im), highest degree first
    ex22 = ([(1, 0), (0, 0), (-1, 0)], [(1, 0), (-2, 0), (0, 0)])
    ex23 = ([(1, 0), (-2 * q, 0), (q * q - 1, 0)], [(mp.mpf(1) / 8000, 0), (0, 0), (0, 0), (-1, 0)])
    n22 = certify("(2,2) z^2-1, (z-1)^2-1", *ex22, R=2.5, grid=24)
    n23 = certify("(2,3) (z-1/10)^2-1, z^3/8000-1", *ex23, R=2.5, grid=30)
    assert (n22, n23) == (6, 10)
    print("ALL PASS")
