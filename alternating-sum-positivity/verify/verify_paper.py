"""Exact checks of every claim in paper.tex (positivity of Abdesselam's sum L).

Run: nice -n 15 ~/.venvs/main/bin/python verify_paper.py   (single core, under a minute)
Mutants at the end must all be KILLED.
"""
from __future__ import annotations

from fractions import Fraction
from math import comb, factorial as f

import sympy as sp


def L(u: int, a: int, b: int, n: int) -> int:
    """The triple sum exactly as defined in the question."""
    tot = Fraction(0)
    for i in range(n + 1):
        for k in range(a + 1):
            for l in range(max(0, n - i - k), min(b, a + b - i - k) + 1):
                tot += Fraction(
                    (-1) ** k * f(u + a + b - i) * f(k + l) * f(a + b - k - l) * f(u + a + b - k - l),
                    f(i) * f(n - i) * f(k) * f(a - k) * f(l) * f(b - l) * f(a + b - k - l - i)
                    * f(k + l - n + i) * f(u + a + b - k - l - i),
                )
    v = tot * f(u + a + b - n)
    assert v.denominator == 1
    return int(v)


def check(name: str, ok: bool) -> None:
    if not ok:
        raise AssertionError(name)
    print("PASS", name)


w, z, N, U = sp.symbols("w z N U")
R = 1 / ((1 - z) ** 2 - w ** 2)


def coeffs(u: int, nu: int, A: int, B: int, expr=None):
    e = (R ** (u + 1) * (R - 1) ** nu) if expr is None else expr
    ser = sp.series(sp.series(e, z, 0, B + 1).removeO(), w, 0, A + 1).removeO()
    return sp.Poly(sp.expand(ser), w, z)


def theorem_ok(u_max=3, nu_max=3, A=6, B=5, expr_fn=None, pref=lambda u, nu: Fraction(f(u + nu) ** 2, f(nu))) -> bool:
    for u in range(u_max + 1):
        for nu in range(nu_max + 1):
            P = coeffs(u, nu, A, B, None if expr_fn is None else expr_fn(u, nu))
            for a in range(A + 1):
                for b in range(B + 1):
                    n = a + b - nu
                    if n < 0:
                        continue
                    if pref(u, nu) * int(P.coeff_monomial(w ** a * z ** b)) != L(u, a, b, n):
                        return False
    return True


# 1. Main theorem
check("Theorem: L = (u+nu)!^2/nu! [w^a z^b] R^(u+1)(R-1)^nu  (u,nu<=3, a<=6, b<=5)", theorem_ok())

# 2. Corollaries
check("L >= 0 and L = 0 for odd a (u<=3, a<=7, b<=5)",
      all(L(u, a, b, n) >= 0 and (a % 2 == 0 or L(u, a, b, n) == 0)
          for u in range(4) for a in range(8) for b in range(6) for n in range(a + b + 1)))
check("extreme case n=a+b equals u!^2 C(2u+a+b+1,b) C(u+a/2,a/2)",
      all(L(u, a, b, a + b) == f(u) ** 2 * comb(2 * u + a + b + 1, b) * comb(u + a // 2, a // 2)
          for u in range(5) for a in range(0, 8, 2) for b in range(6)))
ok = True
for a in range(0, 9, 2):
    for b in range(6):
        for n in range(a + b + 1):
            nu = a + b - n
            pts = [(uu, sp.Rational(L(uu, a, b, n), 1) / sp.Rational(f(uu + nu) ** 2, f(nu))) for uu in range(n + 2)]
            poly = sp.expand(sp.interpolate(pts, U))
            if poly != 0 and any(c < 0 for c in sp.Poly(poly, U).all_coeffs()):
                ok = False
check("Taylor: L/((u+nu)!^2/nu!) has nonnegative coefficients in u (a<=8 even, b<=5)", ok)
# log R has nonnegative coefficients
lg = sp.Poly(sp.expand(sp.series(sp.series(sp.log(R), z, 0, 7).removeO(), w, 0, 7).removeO()), w, z)
check("log R has nonnegative coefficients (degree <= 6)", all(c >= 0 for c in lg.coeffs()))

# 3. Abdesselam's identity for G, with X, Y i.i.d. Beta(1, N-1): E X^p = p!/(N)_p
def rising(x, k):
    out = sp.Integer(1)
    for t in range(k):
        out *= (x + t)
    return out


ok = True
for u in range(3):
    for a in range(0, 5):
        for b in range(0, 4):
            X, Y = sp.symbols("X Y")
            poly = sp.Poly(sp.expand(X ** u * Y ** u * (X - Y) ** a * (X + Y) ** b), X, Y)
            G = sum(c * sp.factorial(p) / rising(N, p) * sp.factorial(q) / rising(N, q)
                    for (p, q), c in zip(poly.monoms(), poly.coeffs()))
            rhs = sp.factorial(a) * sp.factorial(b) / rising(N, u + a + b) ** 2 * sum(
                L(u, a, b, n) * rising(N - 1, n) for n in range(a + b + 1))
            if sp.simplify(G - rhs) != 0:
                ok = False
check("G(u,a,b) = a!b!(N)_{u+a+b}^{-2} sum_n L (N-1)_n as rational functions of N (u<=2, a<=4, b<=3)", ok)

# 4. Example table in the paper: u=1, a=2, b=1
print("   example L(1,2,1,n), n=0..3:", [L(1, 2, 1, n) for n in range(4)])
check("example row L(1,2,1,n) = 0, 72, 48, 12", [L(1, 2, 1, n) for n in range(4)] == [0, 72, 48, 12])
check("example: L(1,2,1,1) = 18 * 4 via the theorem", Fraction(f(3) ** 2, f(2)) * int(coeffs(1, 2, 2, 1).coeff_monomial(w ** 2 * z)) == 72)


# 5. Mutants
def mutant(name, fn):
    try:
        fn()
    except AssertionError:
        print("MUTANT KILLED", name)
        return
    raise SystemExit("MUTANT SURVIVED " + name)


mutant("R^u instead of R^(u+1)", lambda: check("m", theorem_ok(1, 1, 3, 3, lambda u, nu: R ** u * (R - 1) ** nu)))
mutant("prefactor (u+nu)! not squared",
       lambda: check("m", theorem_ok(2, 2, 3, 3, pref=lambda u, nu: Fraction(f(u + nu), f(nu)))))
mutant("R with (1+z)^2", lambda: check("m", theorem_ok(1, 1, 3, 3, lambda u, nu: (1 / ((1 + z) ** 2 - w ** 2)) ** (u + 1) * (1 / ((1 + z) ** 2 - w ** 2) - 1) ** nu)))
print("ALL CHECKS PASSED")

# 6. Taylor's binomial-basis formula and Hucht's 3F2, implemented here from the MathOverflow text
#    (no code shared with ../check.py).
def taylor_inner(a: int, b: int, n: int, m: int) -> int:
    """Taylor's inner sum over d (MO comment, 2 Aug 2025), a even."""
    h = a // 2
    tot = 0
    for d in range(b + 1):
        if 2 * d - b < 0:
            continue
        tot += (-1) ** (b - d) * 2 ** (2 * d - b) * comb(d, 2 * d - b) * comb(h + d, d) * comb(h + d, m + a + b - n)
    return tot


def hyp3f2(p: list, q: list) -> Fraction:
    """Terminating 3F2(p; q; 1) summed term by term with rising factorials; None if a lower
    parameter hits zero before the series terminates."""
    def rf(x: Fraction, k: int) -> Fraction:
        out = Fraction(1)
        for t in range(k):
            out *= x + t
        return out
    tot, k = Fraction(0), 0
    while True:
        num = rf(p[0], k) * rf(p[1], k) * rf(p[2], k)
        if num == 0:
            return tot
        den = rf(q[0], k) * rf(q[1], k) * f(k)
        if den == 0:
            return None
        tot += num / den
        k += 1


ok = True
for nu in range(4):
    for m in range(4):
        P = coeffs(0, 0, 8, 5, R * (R - 1) ** (m + nu))
        for a in range(0, 9, 2):
            for b in range(6):
                n = a + b - nu
                if n < 0 or m > n:
                    continue
                if int(P.coeff_monomial(w ** a * z ** b)) != taylor_inner(a, b, n, m):
                    ok = False
check("Taylor's inner sum = [w^a z^b] R (R-1)^(m+nu)  (a<=8, b<=5, m,nu<=3)", ok)

ok_id, ok_pos = True, True
for a in range(0, 11, 2):
    for b in range(7):
        c = a // 2 + b
        for n in range(a + b + 1):
            nu = a + b - n
            for m in range(n + 1):
                if m + nu > c:
                    continue
                F = hyp3f2([Fraction(1 - b, 2), Fraction(-b, 2), Fraction(m + nu - c)], [Fraction(-c), Fraction(-c)])
                if F is None or Fraction(taylor_inner(a, b, n, m)) != 2 ** b * comb(c, b) * comb(c, m + nu) * F:
                    ok_id = False
                if F is None or F <= 0:
                    ok_pos = False
check("Hucht: inner sum = 2^b C(c,b) C(c,mu+nu) 3F2 for mu+nu <= c (a<=10, b<=6)", ok_id)
check("Hucht's 3F2 > 0 for mu+nu <= c (a<=10, b<=6)", ok_pos)

check("L > 0 exactly when a even and n >= a/2 (u<=2, a<=8, b<=4)",
      all((L(u, a, b, n) > 0) == (a % 2 == 0 and 2 * n >= a)
          for u in range(3) for a in range(9) for b in range(5) for n in range(a + b + 1)))


def degree_ok(shift: int = 0) -> bool:
    for a in range(0, 7, 2):
        for b in range(4):
            for n in range((a + 1) // 2, a + b + 1):
                nu = a + b - n
                pts = [(x, sp.Rational(L(x, a, b, n) * f(nu), f(x + nu) ** 2)) for x in range(n + 2)]
                if sp.degree(sp.expand(sp.interpolate(pts, U)), U) != n - a // 2 + shift:
                    return False
    return True


check("Taylor's degree: exactly n - a/2 in u (a<=6 even, b<=3, n>=a/2)", degree_ok())


def rpow_ok(shift: int = 0) -> bool:
    """Equation (4): [w^(2h) z^y] R^(u+1) = C(u+h,h) C(2u+2h+1+y, y); odd powers of w vanish."""
    for u in range(4):
        P = coeffs(u, 0, 7, 5)
        for x in range(8):
            for y in range(6):
                want = comb(u + x // 2, x // 2) * comb(2 * u + x + 1 + y + shift, y) if x % 2 == 0 else 0
                if int(P.coeff_monomial(w ** x * z ** y)) != want:
                    return False
    return True


check("equation (4): coefficients of R^(u+1) (u<=3, x<=7, y<=5)", rpow_ok())
mutant("equation (4) with 2u+2h+2+y", lambda: check("m", rpow_ok(1)))
mutant("degree n - a/2 + 1", lambda: check("m", degree_ok(1)))
print("ALL EXTRA CHECKS PASSED")
