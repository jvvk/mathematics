"""Fully symbolic degree-2 trace identity: all coefficients and levels are free letters."""
import sys

import sympy as sp

Z, W = sp.symbols("Z W")
p1, p0, q1, q0, s1, s0, t1, t0, r1, r2 = sp.symbols("p1 p0 q1 q0 s1 s0 t1 t0 r1 r2")
F1 = sp.expand((Z**2 + p1 * Z + p0) * (W**2 + s1 * W + s0) - r1)
F2 = sp.expand((Z**2 + q1 * Z + q0) * (W**2 + t1 * W + t0) - r2)
dom = sp.QQ.frac_field(p1, p0, q1, q0, s1, s0, t1, t0, r1, r2)
G = sp.groebner([F1, F2], Z, W, order="grevlex", domain=dom)
lead = [sp.Poly(g, Z, W).monoms(order="grevlex")[0] for g in G.exprs]
basis = [Z**i * W**j for i in range(8) for j in range(8) if not any(i >= a and j >= b for a, b in lead)]
c1, c2, k1, k2 = -p1 / 2, -q1 / 2, -s1 / 2, -t1 / 2
phi = (Z - (c1 + c2) / 2) * (W - (k1 + k2) / 2)
tr = sum(sp.Poly(G.reduce(sp.expand(phi * b))[1], Z, W, domain=dom).coeff_monomial(b) for b in basis)
tr = sp.factor(sp.together(tr))
want = -2 * (c1 - c2) * (k1 - k2)
print("dim", len(basis), "trace", tr, "want", sp.factor(want))
sys.exit(0 if len(basis) == 8 and sp.simplify(tr - want) == 0 else 1)
