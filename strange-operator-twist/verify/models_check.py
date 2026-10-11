"""Checks for Section 6 claims not covered elsewhere (sympy, exact):
1. the centred moments 320 and 6144 of y0(P), which force a completely symmetric certificate's coefficient to be rational;
2. the K3 elliptic fibration of the model of L: Weierstrass data, discriminant, Kodaira types III* (b=0) and I6* (b=oo),
   three I1 fibres, Euler numbers summing to 24, and the discriminant of the cubic factor; the Weierstrass form of
   the model of P obtained by the same substitution;
3. the rational elliptic surface of the remark in Section 2: j = (16x-1)^3/(4x^4), discriminant
   -186624 x^4 (432x^2-40x+1)^3, fibres I4 at 0, III at the roots of 432x^2-40x+1, II at infinity.
MUTANT=1 claims the fibre at b=0 is II* (orders (4,5,10)); it must fail."""
import os
import sympy as sp

MUTANT = os.environ.get("MUTANT") == "1"
t, b, s = sp.symbols("t b s")

# 1. moments
y0 = [1, 16, 576, 25600]
m2 = y0[2] - 2 * 16 * y0[1] + 16**2
m3 = y0[3] - 3 * 16 * y0[2] + 3 * 16**2 * y0[1] - 16**3
assert (m2, m3) == (320, 6144), (m2, m3)

# 2. fibration Y^2 = X^3 + a2 X^2 + a4 X
a2 = b**2 * (1 - 16 * t * (b + 1))
a4 = -16 * t**3 * b**3
c4 = 16 * a2**2 - 48 * a4
c6 = -64 * a2**3 + 288 * a2 * a4
D = 16 * a4**2 * (a2**2 - 4 * a4)
assert sp.expand(D - 4096 * t**6 * b**9 * (b * (1 - 16 * t * (b + 1))**2 + 64 * t**3)) == 0


def order(f, var):
    p = sp.Poly(sp.expand(f), var)
    return min(m[0] for m in p.monoms())


orders0 = (order(c4, b), order(c6, b), order(D, b))
want0 = (4, 5, 10) if MUTANT else (3, 5, 9)
assert orders0 == want0, f"orders at b=0 {orders0}, claimed {want0}"
# at b = oo: s = 1/b, weights 4 and 8 for a K3 (degrees of a2, a4 at most 4, 8)
a2s = sp.expand(s**4 * a2.subs(b, 1 / s))
a4s = sp.expand(s**8 * a4.subs(b, 1 / s))
c4s, c6s = 16 * a2s**2 - 48 * a4s, -64 * a2s**3 + 288 * a2s * a4s
Ds = 16 * a4s**2 * (a2s**2 - 4 * a4s)
assert (order(c4s, s), order(c6s, s), order(Ds, s)) == (2, 3, 12)
cubic = sp.Poly(sp.expand(b * (1 - 16 * t * (b + 1))**2 + 64 * t**3), b)
assert cubic.degree() == 3
disc = sp.factor(sp.discriminant(cubic.as_expr(), b))
assert sp.expand(disc - (-2**20 * t**6 * (4 * t - 1)**2 * (432 * t**2 - 40 * t + 1))) == 0, disc
# Euler numbers: III* = 9, I6* = 12, three I1 = 3
assert 9 + 12 + 3 == 24 and sp.Poly(sp.expand(Ds), s).degree() <= 24
# model of P: V^2 = ab[ab z^2 - 16 t ab z (z+1)^2 (1+a+b) + t^2 (z+1)^4], a cubic in a; with alpha = c3,
# X = alpha a, Y = alpha V gives Y^2 = X^3 + c2 X^2 + c3 c1 X
a, z, X = sp.symbols("a z X")
V2 = a * b * (a * b * z**2 - 16 * t * a * b * z * (z + 1)**2 * (1 + a + b) + t**2 * (z + 1)**4)
h = (z + 1)**2 / z
assert sp.simplify(V2 - a**2 * b**2 * z**2 * (1 - 16 * t * h * (1 + a + b) + t**2 * h**2 / (a * b))) == 0
pc = sp.Poly(sp.expand(V2), a)
c3, c2, c1 = (pc.coeff_monomial(a**k) for k in (3, 2, 1))
assert pc.coeff_monomial(1) == 0
alpha = c3
assert sp.expand(alpha**2 * V2 - ((alpha * a)**3 + c2 * (alpha * a)**2 + c3 * c1 * (alpha * a))) == 0
assert sp.expand(c2 - b**2 * (z**2 - 16 * t * z * (z + 1)**2 * (b + 1))) == 0
assert sp.expand(c3 * c1 + 16 * t**3 * b**3 * z * (z + 1)**6) == 0

# 3. rational elliptic surface Y^2 = 4X^3 - g2 X - g3
x = sp.symbols("x")
q2 = 432 * x**2 - 40 * x + 1
g2 = 3 * (1 - 16 * x) * q2
g3 = (1 - 4 * x) * q2**2
Delta = sp.factor(g2**3 - 27 * g3**2)
assert sp.expand(Delta + 186624 * x**4 * q2**3) == 0, Delta
assert sp.simplify(1728 * g2**3 / (g2**3 - 27 * g3**2) - (16 * x - 1)**3 / (4 * x**4)) == 0
r = sp.solve(q2, x)
assert all(sp.simplify(g2.subs(x, r0)) == 0 and sp.simplify(sp.diff(g2, x).subs(x, r0)) != 0 for r0 in r)  # ord g2 = 1
assert all(sp.simplify(sp.diff(g3, x).subs(x, r0)) == 0 and sp.simplify(sp.diff(g3, x, 2).subs(x, r0)) != 0 for r0 in r)  # ord g3 = 2
assert sp.degree(g2, x) == 3 and sp.degree(g3, x) == 5 and sp.degree(sp.expand(Delta), x) == 10  # orders 1, 1, 2 at infinity: II

print("PASS moments 320, 6144; fibration III* + I6* + 3 I1, Euler 24; cubic discriminant", disc)
print("PASS Weierstrass form of the model of P; rational elliptic surface j, discriminant, fibres I4, III, III, II")
