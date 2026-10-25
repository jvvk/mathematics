"""Exact stability certificate for the five-state example (Proposition in Section 6).

The positive steady states lie on the curve x = Xc(z), y = Yc(z) at the five positive roots of E(z). For each
root take a rational isolating interval I. Each Routh-Hurwitz quantity of the characteristic polynomial
lambda^3 + b1 lambda^2 + b2 lambda + b3 of Df, restricted to the curve, is a rational function q(z) = N(z)/M(z).
If neither N nor M has a real root in the closed interval I (exact Sturm count), q has constant sign on I, so its
sign at the steady state equals its sign at the midpoint of I, computed exactly. States 1, 3, 5 have b1, b3,
b1*b2 - b3 > 0 (asymptotically stable by Routh-Hurwitz); states 2, 4 have det Df > 0, i.e. b3 < 0, so the
characteristic polynomial has a positive real root. States 2 and 4 failing the stability test is the built-in negative
control. Exact rational arithmetic throughout; exits nonzero on failure.
Run: python3 certify_five.py   (needs SymPy; under a minute)
"""
import sys
import sympy as sp

x, y, z, lam = sp.symbols("x y z lam")
R = sp.Rational
V = (x, y, z)
g = [R(1, 2500) - x - x*y + R(2, 5)*y*z + R(1, 100000)*y,
     R(1, 2500) + x + x*z - R(2, 5)*y*z - R(1, 100000)*y,
     5*x - z/2 - R(2, 5)*y*z]
D = 8000*z**2 - 32000*z - 1
Nn = 10000*z**2 + 10000*z + 40
Yc = -Nn/D
Xc = z*(5 + 4*Yc)/50
E = sp.Poly(40000000000*z**5 - 110031000000*z**4 + 50416250000*z**3 - 782738125*z**2 + 101000*z - 1, z)

J = sp.Matrix(g).jacobian(V)
c = sp.Poly(sp.expand((lam*sp.eye(3) - J).det()), lam).all_coeffs()   # [1, b1, b2, b3]
b1, b2, b3 = c[1], c[2], c[3]
quantities = {"b1": b1, "b3": b3, "b1*b2-b3": b1*b2 - b3}
on_curve = {k: sp.factor(sp.together(q.subs({x: Xc, y: Yc}))) for k, q in quantities.items()}

failures = 0


def fail(msg: str) -> None:
    global failures
    failures += 1
    print("FAIL", msg)


ivs = [(sp.Rational(a), sp.Rational(b)) for (a, b), _ in E.intervals(eps=R(1, 10**12))]
ivs = [iv for iv in ivs if iv[1] > 0]
if len(ivs) != 5:
    fail(f"expected five positive roots of E, found {len(ivs)}")
signs = []
for k, (a, b) in enumerate(ivs, 1):
    if E.count_roots(a, b) != 1:
        fail(f"interval {k} does not isolate one root")
    row = {}
    for name, q in on_curve.items():
        num, den = sp.fraction(q)
        pn, pd = sp.Poly(num, z), sp.Poly(den, z)
        if pn.count_roots(a, b) or pd.count_roots(a, b):
            fail(f"state {k}: {name} may change sign on its interval")
            continue
        row[name] = sp.sign(q.subs(z, (a + b) / 2))
    # positivity of the state itself
    for name, expr in (("x", Xc), ("y", Yc)):
        num, den = sp.fraction(sp.together(expr))
        if sp.Poly(num, z).count_roots(a, b) or sp.Poly(den, z).count_roots(a, b) or not sp.sign(expr.subs(z, (a + b) / 2)) > 0:
            fail(f"state {k}: coordinate {name} not certified positive")
    if not a > 0:
        fail(f"state {k}: z not certified positive")
    signs.append(row)
    print(f"state {k}: z in [{float(a):.6g}, {float(b):.6g}]  signs " + ", ".join(f"{n} {int(s):+d}" for n, s in row.items()))

stable = [all(r.get(n) == 1 for n in ("b1", "b3", "b1*b2-b3")) for r in signs]
saddle = [r.get("b3") == -1 for r in signs]
if stable != [True, False, True, False, True]:
    fail(f"stability pattern {stable}, expected states 1, 3, 5 stable")
if [saddle[i] for i in (1, 3)] != [True, True]:
    fail("states 2 and 4: det Df > 0 (b3 < 0) not certified")

print("PASS: five states certified exactly; states 1, 3, 5 stable, 2 and 4 saddles" if not failures else f"{failures} FAILURES")
sys.exit(1 if failures else 0)
