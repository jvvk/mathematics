"""Independent checks of every identity and claim in "Monotonicity of a ratio of complete homogeneous
symmetric polynomials", written from the paper's definitions (h_l by its defining sum over multisets).

  1. Lemma 1: P_l(i) = h_l(1^[n-i], x^[i]) (brute-force multiset sums), degree and leading coefficient,
     positivity on [0, oo) (exact, on a grid), the generating function (2) as a series in z;
  2. Lemma 2 and Proposition 3, symbolically in (t, y) and for the derivative of log Psi;
  3. Lemma 4 (recurrence) and Lemma 5 (the D_l recursion), symbolically;
  4. Lemma 5's conclusions: simple negative zeros, interlacing, positive weights B_r (high precision);
  5. the theorem: Psi_{i,n} strictly increasing on a rational grid in (1, 60], exact arithmetic;
  6. the example l = 1, Psi(1) = 1, the symmetry Psi_{i,n}(x) = Psi_{n-i,n}(1/x), the Meixner identity,
     and the data of Figure 1 parsed from paper.tex.
Planted mutants at the end must all be KILLED.

Run: python3 verify_paper.py      (needs sympy and mpmath; under a minute)
"""

from __future__ import annotations

import itertools
import re
import sys
from fractions import Fraction as Fr
from math import factorial
from pathlib import Path

import mpmath as mp
import sympy as sp

HERE = Path(__file__).resolve().parent
t, y, z = sp.symbols("t y z")
x = 1 + y


def check(name: str, ok: bool) -> None:
    if not ok:
        raise AssertionError(name)
    print("PASS", name, flush=True)


def h(ell: int, xs: list) -> object:
    """h_l by its definition: the sum over multisets of size l of the products."""
    return sum(
        (sp.prod([xs[j] for j in idx]) if idx else 1)
        for idx in itertools.combinations_with_replacement(range(len(xs)), ell)
    )


def P(n, ell: int, tt=t, yy=y) -> sp.Expr:
    """Definition (1)."""
    return sp.expand(
        sum(
            sp.binomial(n + ell - 1, ell - k) * sp.rf(tt, k) / factorial(k) * yy**k
            for k in range(ell + 1)
        )
    )


def H(n: int, ell: int, i: int, xv) -> object:
    return h(ell, [1] * (n - i) + [xv] * i)


def Psi(n: int, ell: int, i: int, xv) -> object:
    return Fr(H(n, ell, i, xv)) ** 2 / (
        Fr(H(n, ell, i + 1, xv)) * Fr(H(n, ell, i - 1, xv))
    )


# ---------- 1. Lemma 1 ----------
ok = True
for n in range(1, 7):
    for ell in range(6):
        p = P(n, ell)
        if (
            sp.Poly(p, t).degree() != ell
            or sp.expand(sp.Poly(p, t).LC() - y**ell / factorial(ell)) != 0
        ):
            ok = False
        for i in range(n + 1):
            if sp.expand(p.subs(t, i) - H(n, ell, i, x)) != 0:
                ok = False
check(
    "Lemma 1: P_l(i) = h_l(1^[n-i], x^[i]), degree l, leading coefficient y^l/l!  (n<=6, l<=5)",
    ok,
)
ok = all(
    P(n, ell, sp.Rational(k, 4), sp.Rational(m, 3)) > 0
    for n in range(1, 7)
    for ell in range(6)
    for k in range(41)
    for m in range(1, 13)
)
check("Lemma 1: P_l > 0 on [0, 10] for y in (0, 4]  (exact grid)", ok)
ok = True
for n in (1, 3, 5):
    F = sp.series((1 - z) ** (-(n - t)) * (1 - (1 + y) * z) ** (-t), z, 0, 6).removeO()
    for ell in range(6):
        if sp.simplify(sp.expand(F.coeff(z, ell)) - P(n, ell)) != 0:
            ok = False
check("Lemma 1: generating function (2), coefficients of z^0..z^5, symbolic t", ok)

# ---------- 2. Lemma 2 and Proposition 3 ----------
ok = all(
    sp.expand(
        y * sp.diff(P(n, ell), y) - ell * P(n, ell) + (n + ell - 1) * P(n, ell - 1)
    )
    == 0
    for n in range(1, 9)
    for ell in range(1, 8)
)
check("Lemma 2: y dP_l/dy = l P_l - (n+l-1) P_(l-1)  (n<=8, l<=7, symbolic)", ok)
ok = True
for n in range(2, 7):
    for ell in range(1, 5):
        f = lambda s: P(n, ell - 1).subs(t, s) / P(n, ell).subs(t, s)
        for i in range(1, n):
            lhs = y * sp.diff(
                sp.log(
                    P(n, ell).subs(t, i) ** 2
                    / (P(n, ell).subs(t, i + 1) * P(n, ell).subs(t, i - 1))
                ),
                y,
            )
            rhs = (n + ell - 1) * (f(i - 1) + f(i + 1) - 2 * f(i))
            if sp.simplify(lhs - rhs) != 0:
                ok = False
check(
    "Proposition 3: (x-1) d/dx log Psi = (n+l-1)(f(i-1)+f(i+1)-2f(i))  (n<=6, l<=4, all i)",
    ok,
)

# ---------- 3. Lemmas 4 and 5 ----------
ok = True
for n in range(1, 8):
    if sp.expand(P(n, 1) - (n + y * t)) != 0:
        ok = False
    for ell in range(1, 7):
        r = (ell + 1) * P(n, ell + 1) - (
            ((1 + x) * ell + n + y * t) * P(n, ell) - x * (n + ell - 1) * P(n, ell - 1)
        )
        if sp.expand(r) != 0:
            ok = False
check("Lemma 4: P_1 = n + yt and recurrence (3)  (n<=7, l<=6)", ok)


def D(n, ell):
    return sp.expand(
        sp.diff(P(n, ell), t) * P(n, ell - 1) - P(n, ell) * sp.diff(P(n, ell - 1), t)
    )


ok = all(sp.expand(D(n, 1) - y) == 0 for n in range(1, 8)) and all(
    sp.expand(
        (ell + 1) * D(n, ell + 1) - (y * P(n, ell) ** 2 + x * (n + ell - 1) * D(n, ell))
    )
    == 0
    for n in range(1, 8)
    for ell in range(1, 6)
)
check("Lemma 5: D_1 = y and recursion (4)  (n<=7, l<=5)", ok)

# ---------- 4. zeros and weights ----------
mp.mp.dps = 50
ok = True
for n in range(1, 11):
    for ell in range(1, 9):
        for yv in (sp.Rational(1, 10), sp.Integer(1), sp.Integer(9)):
            pl = sp.Poly(P(n, ell).subs(y, yv), t)
            plm = sp.Poly(P(n, ell - 1).subs(y, yv), t)
            roots = sorted(sp.re(r) for r in pl.nroots(n=50))
            if len(set(round(float(r), 12) for r in roots)) != ell or max(roots) >= 0:
                ok = False
            if any(abs(sp.im(r)) > 1e-30 for r in pl.nroots(n=50)):
                ok = False
            for r in roots:
                if plm.eval(r) / pl.diff().eval(r) <= 0:
                    ok = False
            if ell >= 2:
                prev = sorted(sp.re(r) for r in plm.nroots(n=50))
                if not all(roots[j] < prev[j] < roots[j + 1] for j in range(ell - 1)):
                    ok = False
check(
    "Lemma 5: l simple negative zeros, interlacing with P_(l-1), weights B_r > 0  (n<=10, l<=8)",
    ok,
)

# ---------- 5. the theorem ----------
grid = [Fr(1) + Fr(k, 8) for k in range(1, 41)] + [Fr(6 + k) for k in range(0, 55, 3)]
grid = sorted(set(grid))
ok = all(
    Psi(n, ell, i, grid[k]) < Psi(n, ell, i, grid[k + 1])
    for n in range(2, 8)
    for ell in range(1, 6)
    for i in range(1, n)
    for k in range(len(grid) - 1)
)
check(
    "Theorem 1: Psi_{i,n} strictly increasing on a rational grid in (1, 60]  (n<=7, l<=5, 1<=i<=n-1)",
    ok,
)

# ---------- 6. examples, symmetry, Meixner, Figure 1 ----------
ok = all(
    Psi(n, 1, i, xv)
    == Fr((n + i * (xv - 1)) ** 2, (n + i * (xv - 1)) ** 2 - (xv - 1) ** 2)
    for n in range(2, 9)
    for i in range(1, n)
    for xv in (Fr(3, 2), Fr(5), Fr(7, 3))
)
check("example l = 1: Psi = (n+iy)^2/((n+iy)^2 - y^2)", ok)
check(
    "Psi_{i,n}(1) = 1",
    all(
        Psi(n, ell, i, Fr(1)) == 1
        for n in range(2, 7)
        for ell in range(1, 5)
        for i in range(1, n)
    ),
)
ok = all(
    Psi(n, ell, i, 1 / xv) == Psi(n, ell, n - i, xv)
    for n in range(2, 7)
    for ell in range(1, 5)
    for i in range(1, n)
    for xv in (Fr(3, 2), Fr(4), Fr(9, 7))
)
check("symmetry Psi_{i,n}(1/x) = Psi_{n-i,n}(x)", ok)
ok = True
for n in range(1, 6):
    for ell in range(6):
        meixner = sp.hyper([-ell, t], [n], -y)  # M_l(-t; n, 1/x) = 2F1(-l, t; n; 1 - x)
        series = sum(
            sp.rf(-ell, k) * sp.rf(t, k) / (sp.rf(n, k) * factorial(k)) * (-y) ** k
            for k in range(ell + 1)
        )
        if sp.expand(sp.binomial(n + ell - 1, ell) * series - P(n, ell)) != 0:
            ok = False
check("Meixner: P_l(t) = C(n+l-1, l) * 2F1(-l, t; n; -y)", ok)

tex = (HERE.parent / "paper" / "paper.tex").read_text()
curve = re.findall(r"\\addplot\[thick,blue\] coordinates \{([^}]*)\}", tex)[0]
dots = re.findall(r"\\addplot\[only marks[^\]]*\] coordinates \{([^}]*)\}", tex)[0]
nF, lF, yF = 6, 3, sp.Integer(1)
fF = sp.lambdify(t, P(nF, lF - 1).subs(y, yF) / P(nF, lF).subs(y, yF))
pairs = [tuple(map(float, p)) for p in re.findall(r"\(([-\d.]+),([-\d.]+)\)", curve)]
check(
    "Figure 1: plotted curve is f = P_2/P_3 for n = 6, x = 2 (to 4 decimals)",
    all(abs(fF(a) - b) < 6e-5 for a, b in pairs),
)
pts = [tuple(map(float, p)) for p in re.findall(r"\(([-\d.]+),([-\d.]+)\)", dots)]
check(
    "Figure 1: red points are f(0..6)",
    [a for a, _ in pts] == list(range(7))
    and all(abs(fF(a) - b) < 6e-5 for a, b in pts),
)
zs = sorted(float(sp.re(r)) for r in sp.Poly(P(nF, lF).subs(y, yF), t).nroots())
check(
    "Figure 1: zeros of P_3 are -16.45, -8, -2.55",
    abs(zs[0] + 16.446) < 1e-3 and abs(zs[1] + 8) < 1e-12 and abs(zs[2] + 2.554) < 1e-3,
)
check(
    "Figure 1: f strictly convex at 1..5 (second differences > 0)",
    all(fF(k - 1) + fF(k + 1) - 2 * fF(k) > 0 for k in range(1, 6)),
)


# ---------- mutants ----------
def mutant(name, fn):
    try:
        fn()
    except AssertionError:
        print("MUTANT KILLED", name)
        return
    sys.exit("MUTANT SURVIVED " + name)


mutant(
    "Lemma 2 with (n+l) in place of (n+l-1)",
    lambda: check(
        "m",
        all(
            sp.expand(
                y * sp.diff(P(n, ell), y) - ell * P(n, ell) + (n + ell) * P(n, ell - 1)
            )
            == 0
            for n in range(1, 5)
            for ell in range(1, 5)
        ),
    ),
)
mutant(
    "recurrence with x(n+l)",
    lambda: check(
        "m",
        all(
            sp.expand(
                (ell + 1) * P(n, ell + 1)
                - (
                    ((1 + x) * ell + n + y * t) * P(n, ell)
                    - x * (n + ell) * P(n, ell - 1)
                )
            )
            == 0
            for n in range(1, 5)
            for ell in range(1, 5)
        ),
    ),
)
mutant(
    "Psi decreasing",
    lambda: check(
        "m",
        all(
            Psi(n, ell, i, grid[k]) > Psi(n, ell, i, grid[k + 1])
            for n in range(2, 5)
            for ell in range(1, 4)
            for i in range(1, n)
            for k in range(5)
        ),
    ),
)
mutant(
    "symmetry with n-i-1",
    lambda: check(
        "m",
        all(
            Psi(n, ell, i, 1 / xv) == Psi(n, ell, n - i - 1, xv)
            for n in range(3, 6)
            for ell in range(1, 4)
            for i in range(1, n - 1)
            for xv in (Fr(3, 2),)
        ),
    ),
)
mutant(
    "P_l(i) = h_l(1^[n-i+1], x^[i-1])",
    lambda: check(
        "m",
        all(
            sp.expand(P(n, ell).subs(t, i) - H(n, ell, i - 1, x)) == 0
            for n in range(2, 5)
            for ell in range(1, 4)
            for i in range(1, n + 1)
        ),
    ),
)
mutant(
    "Figure 1 with x = 3",
    lambda: check(
        "m",
        all(
            abs(sp.lambdify(t, P(6, 2).subs(y, 2) / P(6, 3).subs(y, 2))(a) - b) < 6e-5
            for a, b in pts
        ),
    ),
)
print("ALL CHECKS PASSED")
