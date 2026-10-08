"""Independent recheck (shares no code with certify_points.py).

For each example, treat z and conj(z) as independent: F_k(Z, W) = f_k(Z) g_k(W) - r_k with g_k the
conjugate-coefficient polynomial (here f_k has real coefficients, so g_k = f_k).
1. R(Z) = Res_W(F1, F2) exactly (sympy, rational arithmetic); deg R = 2 n1 n2 here.
2. All roots Z of R to 60 digits; for each, the common root W.
3. Real intersection points = solutions with W = conj(Z); count them.
4. Trace identity: sum over all 2 n1 n2 solutions of (Z - m)(W - conj m) = -(n1 n2 / 2)|c1 - c2|^2,
   c_k = centroid of the roots of f_k, m = (c1 + c2)/2.

    python3 recheck.py
"""
import sympy as sp
import mpmath as mp

mp.mp.dps = 60
Z, W = sp.symbols("Z W")


def run(name, f1, f2, r1, r2, expect_real):
    F1 = sp.expand(f1(Z) * f1(W) - r1)
    F2 = sp.expand(f2(Z) * f2(W) - r2)
    R = sp.Poly(sp.resultant(F1, F2, W), Z)
    n1, n2 = sp.degree(f1(Z), Z), sp.degree(f2(Z), Z)
    assert R.degree() == 2 * n1 * n2, R.degree()
    assert sp.gcd(R, R.diff(Z)).degree() == 0  # simple roots: every solution has multiplicity one
    roots = mp.polyroots([mp.mpf(sp.Rational(c).p) / sp.Rational(c).q for c in R.all_coeffs()],
                         maxsteps=500, extraprec=400)
    sols = []
    for z in roots:
        c1 = [sp.lambdify(Z, c, "mpmath")(z) for c in sp.Poly(F1, W).all_coeffs()]
        c2 = [sp.lambdify(Z, c, "mpmath")(z) for c in sp.Poly(F2, W).all_coeffs()]
        w1 = mp.polyroots(c1, maxsteps=200, extraprec=200)
        w2 = mp.polyroots(c2, maxsteps=200, extraprec=200)
        w = min(((a, b) for a in w1 for b in w2), key=lambda t: abs(t[0] - t[1]))
        assert abs(w[0] - w[1]) < mp.mpf(10) ** -30
        sols.append((z, w[0]))
    real = [s for s in sols if abs(s[1] - mp.conj(s[0])) < mp.mpf(10) ** -30]
    def centroid(f, n):  # root sum / degree = -(next coefficient) / (n * leading coefficient), exact
        c = sp.Poly(f(Z), Z).all_coeffs()
        q = sp.Rational(-c[1] / (n * c[0]))
        return mp.mpf(q.p) / q.q
    ce1, ce2 = centroid(f1, n1), centroid(f2, n2)
    m = (ce1 + ce2) / 2
    T = sum((s[0] - m) * (s[1] - mp.conj(m)) for s in sols)
    target = -(n1 * n2 / mp.mpf(2)) * abs(ce1 - ce2) ** 2
    print(f"{name}: {len(sols)} complex solutions, {len(real)} real points; "
          f"trace {mp.nstr(T, 20)} vs -(n1 n2/2)|c1-c2|^2 = {mp.nstr(target, 20)}")
    assert len(real) == expect_real and abs(T - target) < mp.mpf(10) ** -15
    return sols, real, m


sols, real, m = run("(2,2)", lambda z: z**2 - 1, lambda z: (z - 1)**2 - 1, 1, 1, 6)
# Figure 2 numbers: the sigma-pair is (1/2 -+ t, 1/2 +- t), t^2 = 5/4 + sqrt 2; each contributes
# -(5/4 + sqrt 2); the six real points contribute 1/2 + 2 sqrt 2.
t = mp.sqrt(mp.mpf(5) / 4 + mp.sqrt(2))
pair = [s for s in sols if s not in real]
assert len(pair) == 2
for z, w in pair:
    assert min(abs(z - (m - t)), abs(z - (m + t))) < mp.mpf(10) ** -30 and abs(z + w - 1) < mp.mpf(10) ** -30
    assert abs((z - m) * (w - m) + (mp.mpf(5) / 4 + mp.sqrt(2))) < mp.mpf(10) ** -30
assert abs(sum(abs(z - m) ** 2 for z, w in real) - (mp.mpf(1) / 2 + 2 * mp.sqrt(2))) < mp.mpf(10) ** -30
print("(2,2) sigma-pair (1/2 -+ t, 1/2 +- t), t^2 = 5/4 + sqrt2: each -(5/4 + sqrt2); real part 1/2 + 2 sqrt2: OK")
run("(2,3)", lambda z: (z - sp.Rational(1, 10))**2 - 1, lambda z: z**3 / 8000 - 1, 1, 1, 10)
# Remark 14 and Corollary 3: M(n1, n2) = n1 n2 + n2 + d e (Orevkov-Pakovich), against 2 n1 n2 - 2.
from math import gcd
def M(a, b):
    d = gcd(a, b)
    return a * b + b + d * (1 if (a // d) % 2 == 0 else 0)
assert (M(2, 2), M(2, 3), M(2, 4), M(3, 3)) == (6, 10, 12, 12)
eq = [(a, b) for a in range(2, 60) for b in range(a, 60) if M(a, b) == 2 * a * b - 2]
assert eq == [(2, 2), (2, 3)], eq
print("M(2,2)=6, M(2,3)=10, M(2,4)=12, M(3,3)=12; M = 2 n1 n2 - 2 for 2 <= n1 <= n2 < 60 only at (2,2), (2,3): OK")
print("ALL PASS")
