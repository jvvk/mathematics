"""Checks for "An integral of hyperbolic tangents" (MSE 5150767). Every claim has a mutant that must fail.

    timeout 3600 nice -n 15 python3 check.py        (about 3 minutes; needs mpmath and sympy)

C1  Theorem 1: the residue formula reproduces the exact power-series coefficients c_n(N) for 2 <= n <= 15
    (all poles, N <= 3n^2), and agrees with a numerical limit at the first poles.
C2  inversion: a_m(-j) = (-1)^(n+1) a_m(j) for n <= 15.
C3  Lemma 2 for all moduli Q <= 40 and all N, |N| <= 3Q; Montgomery-Vaughan 9.7 with the conjugate (and not without).
C4  Theorem 3: the character form equals quadrature to 1e-25 for 2 <= n <= 11 and the question's values for
    n = 3, 5, 7, 9, 11; the coefficients quoted in Section 3 (n = 5, 7, 9 against the question's characters);
    the log coefficient 208/21 at n = 9; rational log coefficients for odd n <= 13.
C5  Corollary 4 and Table 1: the cotangent symmetry for m < 30; the family table; the conductor sets equal the
    question's for odd n <= 15 (apart from conductor 1); a conductor f > 1 only through a family with f | 2m and
    rho' >= 1; K_1 = 0 at n = 3 and 7.
C6  Section 5: the functional-equation constant ln 2 pi - 1 + gamma with -ln f, for every even primitive character of
    conductor <= 16; sum K L(-1) = 0 for odd n <= 13; the weights 4, 8, 40/3 and -40 -+ 8/sqrt 5.
C7  I_3 = ln(27/4) and the question's closed forms for I_5, I_7 and I_9 (evaluated independently).
"""

from __future__ import annotations

import sys
from fractions import Fraction
from math import gcd

import mpmath as mp

import characters as Ch
import residues as R

mp.mp.dps = 40
results: list[bool] = []


def report(name: str, good: bool, caught: bool) -> None:
    results.append(good and caught)
    print(
        f"{'PASS' if good else 'FAIL'} {name}   (mutant {'caught' if caught else 'MISSED'})",
        flush=True,
    )


def close(a, b, tol=1e-20) -> bool:
    return abs(mp.mpc(a) - mp.mpc(b)) < tol


# C1
err = max(R.check(n) for n in range(2, 16))
report(
    "C1 residue formula = exact series, 2 <= n <= 15",
    err < 1e-15,
    R.check(7, mutant=True) > 1e-3,
)


# C2
def inv_ok(n: int, sign: int) -> bool:
    for m, j in R.poles(n):
        if not close(
            R.a_formula(n, m, (2 * m - j) % (2 * m)), sign * R.a_formula(n, m, j), 1e-25
        ):
            return False
    return True


report(
    "C2 a_m(-j) = (-1)^(n+1) a_m(j), n <= 15",
    all(inv_ok(n, (-1) ** (n + 1)) for n in range(2, 16)),
    not all(inv_ok(n, (-1) ** n) for n in range(2, 16)),
)

# C3
ge = Ch.gauss_identity_check()


def mv97(conj: bool) -> int:
    bad = 0
    for f in range(3, 30):
        for ch in Ch.characters(f):
            if Ch.conductor(ch, f) != f:
                continue
            tab = Ch.primitive_table(ch, f, f)
            tau = Ch.gauss(tab)
            for n in range(-2 * f, 2 * f):
                s = mp.fsum(tab[a] * Ch.e(mp.mpf(a * n) / f) for a in range(f))
                v = mp.conj(tab[n % f]) if conj else tab[n % f]
                bad += abs(s - v * tau) > 1e-20
    return bad


report(
    "C3 Lemma 2 for Q <= 40; MV 9.7 holds with conj",
    ge < 1e-20 and mv97(True) == 0,
    mv97(False) > 0,
)

# C4
ASKER = {
    3: "1.9095425048844384553",
    5: "1.7518763852341610453",
    7: "1.7203912772183856179",
    9: "1.7110140692970610143",
    11: "1.7076399598357368455",
}
dec = {n: Ch.decompose(n) for n in range(2, 14)}
quad_ok = True
for n in range(2, 12):
    out, logs = dec[n]
    I = Ch.I_from(out, logs)
    quad_ok &= abs(I - Ch.I_quad(n)) < 1e-25 and abs(I.imag) < 1e-25
    if n in ASKER:
        quad_ok &= abs(I.real - mp.mpf(ASKER[n])) < 1e-18


def K_of(n: int, table: dict[int, complex]) -> mp.mpc:
    """K for the primitive character with the given values on residues (dict r -> value), 0 if absent."""
    out, _ = dec[n]
    for tab, K in out.values():
        f = len(tab)
        if f == max(table) + 1 or (f == 1 and max(table) == 0):
            if all(close(tab[r % f], v, 1e-15) for r, v in table.items()):
                return K
    return mp.mpc(0)


w = mp.expj(2 * mp.pi / 3)
chi8 = {1: 1, 3: -1, 5: -1, 7: 1}
chi5 = {1: 1, 2: -1, 3: -1, 4: 1}
chi12 = {1: 1, 5: -1, 7: -1, 11: 1}
chi7 = {1: 1, 2: w**2, 3: w, 4: w, 5: w**2, 6: 1}
chi16 = {1: 1, 3: 1j, 5: -1j, 7: -1, 9: -1, 11: -1j, 13: 1j, 15: 1}
triv = {0: 1}
coef_ok = (
    close(K_of(5, chi8), 4)
    and close(K_of(5, triv), -48)
    and close(K_of(7, chi5), 20)
    and close(K_of(7, chi12), -4)
    and close(K_of(7, triv), 0)
    and close(K_of(3, triv), 0)
    and close(K_of(9, chi7), -20 - 4 * mp.sqrt(3) * 1j)
    and close(
        K_of(9, {r: mp.conj(v) for r, v in chi7.items()}), -20 + 4 * mp.sqrt(3) * 1j
    )
    and close(K_of(9, chi16), 2 - 2j)
    and close(K_of(9, {r: mp.conj(v) for r, v in chi16.items()}), 2 + 2j)
)
log9 = dec[9][1].get(2, 0)
rational = True
for n in (3, 5, 7, 9, 11, 13):
    for p, c in dec[n][1].items():
        fr = Fraction(float(c.real)).limit_denominator(10**5)
        rational &= (
            abs(c.imag) < 1e-20
            and abs(c.real - mp.mpf(fr.numerator) / fr.denominator) < 1e-18
        )
# mutant: drop the Euler factor H (g^2 prod) -> the value at n = 11 moves
saved = Ch.mobius
Ch.mobius = lambda n: 1 if n == 1 else 0
out_m, logs_m = Ch.decompose(11)
Ch.mobius = saved
caught = abs(Ch.I_from(out_m, logs_m) - Ch.I_quad(11)) > 1e-6
report(
    "C4 Theorem 3 = quadrature (n <= 11) and the question's values; quoted K; 208/21 ln 2; rational logs",
    quad_ok and coef_ok and close(log9, mp.mpf(208) / 21) and rational,
    caught,
)

# C5

sym_ok = True
for m in range(2, 30):
    for rho in range(m):
        for j in (x for x in range(1, 2 * m) if gcd(x, 2 * m) == 1):
            A = mp.fprod(mp.cot(mp.pi * j * k / (2 * m)) for k in range(1, rho + 1))
            B = mp.fprod(mp.cot(mp.pi * j * k / (2 * m)) for k in range(1, m - rho))
            eps = mp.tan(mp.pi * j / 4) if m % 2 == 0 else 1
            sym_ok &= abs(A - eps * B) < 1e-18
TABLE = {
    9: {1: (0, 0), 3: (0, 0), 5: (4, 0), 6: (3, 2), 7: (2, 2), 8: (1, 1), 9: (0, 0)},
    11: {
        1: (0, 0),
        2: (1, 0),
        3: (2, 0),
        6: (5, 0),
        7: (4, 2),
        8: (3, 3),
        9: (2, 2),
        10: (1, 1),
        11: (0, 0),
    },
    13: {
        1: (0, 0),
        4: (1, 1),
        7: (6, 0),
        8: (5, 2),
        9: (4, 4),
        10: (3, 3),
        11: (2, 2),
        12: (1, 1),
        13: (0, 0),
    },
    15: {
        1: (0, 0),
        2: (1, 0),
        3: (0, 0),
        4: (3, 0),
        5: (0, 0),
        8: (7, 0),
        9: (6, 2),
        10: (5, 4),
        11: (4, 4),
        12: (3, 3),
        13: (2, 2),
        14: (1, 1),
        15: (0, 0),
    },
}
ASKERC = {
    3: {1},
    5: {1, 8},
    7: {1, 5, 12},
    9: {1, 7, 8, 12, 16},
    11: {1, 5, 7, 8, 9, 16, 20},
    13: {1, 5, 8, 9, 11, 12, 16, 20, 24},
    15: {1, 5, 7, 8, 9, 11, 12, 13, 20, 24, 28},
}


def fams(n, use_rho_prime=True):
    return {
        m: (n % m, min(n % m, m - 1 - n % m) if use_rho_prime else n % m)
        for m in range(1, n + 1)
        if (n // m) % 2
    }


def rule_ok(n, conds, use_rho_prime=True):
    live = [m for m, (_, rp) in fams(n, use_rho_prime).items() if rp >= 1]
    pred = {f for m in live for f in range(2, 2 * m + 1) if (2 * m) % f == 0}
    return all(f in pred for f in conds if f > 1) and (use_rho_prime or True)


cond_ok, rule = True, True
for n in (3, 5, 7, 9, 11, 13, 15):
    out, _ = dec[n] if n in dec else Ch.decompose(n)
    got = {len(t) for t, K in out.values() if abs(K) > 1e-20}
    cond_ok &= got - {1} == ASKERC[n] - {1}
    rule &= rule_ok(n, got)
    if n in TABLE:
        cond_ok &= fams(n) == TABLE[n]
# mutant: with rho in place of rho', conductor 16 would be predicted at n = 15 (family m = 8 has rho = 7 >= 1)
live15 = [m for m, (_, r) in fams(15, False).items() if r >= 1]
caught = 8 in live15 and 16 not in {
    len(t) for t, K in Ch.decompose(15)[0].values() if abs(K) > 1e-20
}
report(
    "C5 cotangent symmetry; Table 1; conductor sets = question's (odd n <= 15); conductor rule",
    sym_ok and cond_ok and rule,
    caught,
)

# C6
c = mp.log(2 * mp.pi) - 1 + mp.euler


def fe_ok(sign: int) -> bool:
    ok = True
    for f in range(1, 17):
        for ch in Ch.characters(f):
            if Ch.conductor(ch, f) != f:
                continue
            tab = Ch.primitive_table(ch, f, f) if f > 1 else (mp.mpc(1),)
            if f > 1 and not close(tab[f - 1], 1):
                continue
            cj = tuple(mp.conj(z) for z in tab)
            a = Ch.Lfun(-1, tab, 1) / Ch.Lfun(-1, tab)
            b = Ch.Lfun(2, cj, 1) / Ch.Lfun(2, cj)
            ok &= abs(a + b + sign * mp.log(f) - c) < 1e-20
    return ok


sumzero = all(
    abs(mp.fsum(K * Ch.Lfun(-1, t) for t, K in dec[n][0].values())) < 1e-20
    for n in (3, 5, 7, 9, 11, 13)
)


def W(n, table):
    out, _ = dec[n]
    for tab, K in out.values():
        if len(tab) == max(table) + 1 and all(
            close(tab[r % len(tab)], v, 1e-15) for r, v in table.items()
        ):
            return -K * Ch.Lfun(-1, tab)
    return None


w11 = sorted(
    (
        -K * Ch.Lfun(-1, t)
        for t, K in dec[13][0].values()
        if len(t) == 11 and abs(K) > 1e-20
    ),
    key=lambda z: float(mp.re(z)),
)
s5 = 8 / mp.sqrt(5)
weights_ok = (
    close(W(5, chi8), 4)
    and close(W(5, triv), -4)
    and close(W(7, chi5), 8)
    and close(W(7, chi12), -8)
    and close(W(11, triv), mp.mpf(40) / 3)
    and len(w11) == 4
    and all(close(z, -40 - s5, 1e-15) for z in w11[:2])
    and all(close(z, -40 + s5, 1e-15) for z in w11[2:])
)
report(
    f"C6 FE constant with -ln f; sum K L(-1) = 0; weights 4, 8, 40/3, -40 -+ 8/sqrt5 ({len(w11)} conductor-11 chars)",
    fe_ok(1) and sumzero and weights_ok,
    not fe_ok(-1),
)

# C7
eta1 = -3 * mp.zeta(-1, derivative=1) - mp.log(2) / 3  # eta'(-1)
L = lambda tab, d=1: Ch.Lfun(-1, tuple(tab), d)
t8 = [0, 1, 0, -1, 0, -1, 0, 1]
t5 = [0, 1, -1, -1, 1]
t12 = [0, 1, 0, 0, 0, -1, 0, -1, 0, 0, 0, 1]
t7 = [0] + [chi7[r] for r in range(1, 7)]
t16 = [chi16.get(r, 0) for r in range(16)]
ln = mp.log
I5 = 4 * ln(4) - 3 * ln(3) - 5 * ln(5) + 16 * eta1 + 4 * L(t8)
I7 = (
    10 * ln(5)
    + 7 * ln(7)
    - 12 * ln(3)
    - mp.mpf(68) / 5 * ln(2)
    + 20 * L(t5)
    - 4 * L(t12)
)
I9 = (
    32 * eta1
    + mp.mpf(144) / 7 * ln(2)
    + 3 * ln(3)
    - 5 * ln(5)
    - 21 * ln(7)
    + 8 * L(t8)
    + 8 * L(t12)
    - 4 * mp.re((10 + 2j * mp.sqrt(3)) * L(t7))
    + 4 * mp.re((1 - 1j) * L(t16))
)
forms = [(3, ln(mp.mpf(27) / 4)), (5, I5), (7, I7), (9, I9)]
good = all(abs(v - Ch.I_quad(n)) < 1e-20 for n, v in forms)
report(
    "C7 I_3 = ln(27/4) and the question's closed forms for I_5, I_7, I_9",
    good,
    abs(ln(mp.mpf(27) / 4) - Ch.I_quad(5)) > 1e-3,
)

print("ALL PASS" if all(results) else "SOME FAIL")
sys.exit(0 if all(results) else 1)
