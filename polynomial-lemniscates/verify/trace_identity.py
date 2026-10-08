"""Exact check of the trace identity
    sum over the 2 n1 n2 solutions of P1(Z) P1*(W) = r1, P2(Z) P2*(W) = r2 of
    (Z - m)(W - m*) = -n1 n2 |c1 - c2|^2 / 2,  m = (c1 + c2)/2, c_k = centroid of roots of P_k,
with Z, W independent and P* the conjugate-coefficient polynomial (treated as independent letters).
Method: trace of multiplication by phi on Q(params)[Z, W]/(F1, F2), via a Groebner basis.
Exits nonzero on any failure; MUTANT=1 plants a wrong right-hand side."""
from __future__ import annotations

import os
import random
import sys

import sympy as sp

Z, W = sp.symbols("Z W")
MUTANT = os.environ.get("MUTANT") == "1"


def trace(phi, F1, F2):
    G = sp.groebner([F1, F2], Z, W, order="grevlex")
    # monomial basis of the quotient: standard monomials
    lead = [sp.Poly(g, Z, W).monoms(order="grevlex")[0] for g in G.exprs]
    basis = []
    for i in range(12):
        for j in range(12):
            if not any(i >= a and j >= b for a, b in lead):
                basis.append(Z**i * W**j)
    tr = 0
    for b in basis:
        red = G.reduce(sp.expand(phi * b))[1]
        tr += sp.Poly(red, Z, W).coeff_monomial(b)
    return sp.nsimplify(tr), len(basis)


def case(n1: int, n2: int, symbolic_r: bool, rng: random.Random) -> bool:
    def rpoly(var, n):
        return sp.expand(sp.prod([var - sp.Rational(rng.randint(-9, 9), rng.randint(1, 4)) for _ in range(n)]) +
                         rng.randint(-3, 3))
    # independent "conjugate" polynomials: random monic, as letters (identity is algebraic in them)
    P1, P2 = rpoly(Z, n1), rpoly(Z, n2)
    Q1, Q2 = rpoly(W, n1), rpoly(W, n2)
    r1, r2 = (sp.symbols("r1 r2") if symbolic_r else (rng.randint(1, 9), rng.randint(1, 9)))
    F1, F2 = sp.expand(P1 * Q1 - r1), sp.expand(P2 * Q2 - r2)
    cen = lambda P, v: -sp.Poly(P, v).all_coeffs()[1] / sp.Poly(P, v).degree()  # noqa: E731
    c1, c2, k1, k2 = cen(P1, Z), cen(P2, Z), cen(Q1, W), cen(Q2, W)
    m, mk = (c1 + c2) / 2, (k1 + k2) / 2
    tr, N = trace((Z - m) * (W - mk), F1, F2)
    want = -sp.Rational(n1 * n2, 2) * (c1 - c2) * (k1 - k2)
    if MUTANT:
        want = -sp.Rational(n1 * n2, 4) * (c1 - c2) * (k1 - k2)
    ok = N == 2 * n1 * n2 and sp.simplify(tr - want) == 0
    print(f"n=({n1},{n2}) r symbolic={symbolic_r} dim={N} trace={sp.simplify(tr)} want={want} {'OK' if ok else 'FAIL'}")
    return ok


rng = random.Random(2026)
results = []
for n1, n2, sym in [(2, 2, True), (2, 2, True), (2, 2, False), (2, 2, False), (2, 3, False), (3, 3, False)]:
    results.append(case(n1, n2, sym, rng))
sys.exit(0 if all(results) else 1)
