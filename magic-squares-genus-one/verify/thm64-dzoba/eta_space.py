"""Definitions for mutants.py: the 45-coefficient ansatz Q(x, l) (linear in x, quartic in l), eta's numerator, and
the cell-line (reflexive) conditions.

Release note (22 November 2026): the original file also derived the node conditions and ran a dimension count.
That derivation was wrong (it rejected the ten forms (l.x)K(l), which vanish identically as differentials), so it
has been removed. The node check used is check_triple in eta_regular.py; the dimension count is in mutants.py.
"""
from __future__ import annotations

import itertools

import sympy as S

from eta_regular import CELLS, L, X, dp, dw, dX, dy, e, frame, l0, l1, l2, p, triple_points, u, v, w, y

MONS = [m for m in itertools.product(range(5), repeat=3) if sum(m) == 4]
C = S.symbols(f"c0:{3 * len(MONS)}")


def Qgen(x, W):
    out = 0
    n = 0
    for i in range(3):
        for m in MONS:
            out += C[n] * x[i] * W[0] ** m[0] * W[1] ** m[1] * W[2] ** m[2]
            n += 1
    return out


def eta_Q(x, W):
    F = l1**3 - l0**2 * l1
    G = l2**3 - l0**2 * l2
    sub = dict(zip((l0, l1, l2), W))
    gF = S.Matrix([S.diff(F, s) for s in (l0, l1, l2)]).subs(sub)
    gG = S.Matrix([S.diff(G, s) for s in (l0, l1, l2)]).subs(sub)
    return S.Matrix.hstack(x, gF, gG).det()


def line_eqs(Qf):
    eqs = []
    for a, b in CELLS:
        Lk = e + a * u + b * v
        x, dx = frame([3 * e + 5 * u + 7 * v + 2 * Lk, 11 * e - 13 * u + 17 * v, Lk])
        Q = S.expand(Qf(x, x.cross(dx)))
        for (i, j), c in S.Poly(Q, dp, dy).terms():
            if j < 2:
                eqs += S.Poly(S.expand(c.subs(y, 0)), p).coeffs()
    return eqs


def solve_space(eqs):
    M = S.Matrix([[S.expand(eq).coeff(ci) for ci in C] for eq in eqs]) if eqs else S.zeros(0, len(C))
    return M.nullspace()


def as_Q(vec):
    return lambda x, W: Qgen(x, W).subs(dict(zip(C, vec)))
