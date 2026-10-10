"""Character form of I_n (MSE q/5150767).

From residues.py: c_n(N) = sum_{m: floor(n/m) odd} sum_{j in U(2m)} a(m,j) e(-jN/(2m)).
Expand a(m, .) = sum_{chi mod 2m} alpha_{m,chi} chi(.). For chi induced by primitive chi* mod f, g = 2m/f,
    sum_{j in U(2m)} chi(j) e(-jN/2m) = chi*(-1) tau(chi*) sum_{d | (N,g)} d mu(g/d) chi*(g/d) conj(chi*)(N/d),
so  D_n(s) = sum_{m,chi} alpha chi*(-1) tau(chi*) L(s, conj chi*) H(s),  H(s) = sum_{d|g} mu(g/d) chi*(g/d) d^{1-s},
and I_n = -2 D_n'(-1).  This script checks:
  (a) the Gauss-sum identity above (all q <= 40, all chi, |N| <= 3q);
  (b) I_n from the character form = I_n by quadrature (n = 2..11);
  (c) the asker's closed forms for n = 3, 5, 7, 9;
and prints the coefficient of L'(-1, psi) for each primitive psi, with W = K * L(-1, psi).
"""

from __future__ import annotations

import sys
from functools import lru_cache
from math import gcd

import mpmath as mp
from sympy import factorint, primitive_root

from residues import a_formula, poles


def mobius(n: int) -> int:
    fac = factorint(n)
    return 0 if any(v > 1 for v in fac.values()) else (-1) ** len(fac)

mp.mp.dps = 30


def e(x):
    return mp.expj(2 * mp.pi * x)


@lru_cache(None)
def characters(q: int) -> list[tuple[int, tuple[int, ...]]]:
    """All characters mod q as (L, t): chi(x) = e(t[x]/L) on units, t[x] = -1 off units."""
    from itertools import product
    from math import lcm

    gens: list[tuple[int, int]] = []  # (generator mod q, order)
    for p, k in factorint(q).items():
        pk, rest = p ** k, q // p ** k

        def lift(x: int) -> int:  # CRT: x mod pk, 1 mod rest
            return next(y for y in range(x % pk, q + 1, pk) if y % rest == 1 % rest)

        if p == 2:
            if k >= 2:
                gens.append((lift(pk - 1), 2))
            if k >= 3:
                gens.append((lift(5), 2 ** (k - 2)))
        else:
            gens.append((lift(primitive_root(pk)), (p - 1) * p ** (k - 1)))
    logs: dict[int, tuple[int, ...]] = {1 % q: (0,) * len(gens)}
    frontier = [1 % q]
    while frontier:
        nxt = []
        for x in frontier:
            for i, (g, o) in enumerate(gens):
                y = x * g % q
                if y not in logs:
                    v = list(logs[x]); v[i] = (v[i] + 1) % o
                    logs[y] = tuple(v); nxt.append(y)
        frontier = nxt
    assert len(logs) == sum(1 for x in range(q) if gcd(x, q) == 1)
    L = lcm(1, *[o for _, o in gens])
    return [(L, tuple(sum(ks[i] * logs[x][i] * (L // gens[i][1]) for i in range(len(gens))) % L
                      if x in logs else -1 for x in range(q)))
            for ks in product(*[range(o) for _, o in gens])]


def chival(ch, x: int):
    L, t = ch
    v = t[x % len(t)]
    return mp.mpc(0) if v < 0 else e(mp.mpf(v) / L)


def conductor(ch, q: int) -> int:
    for f in sorted(d for d in range(1, q + 1) if q % d == 0):
        if all(
            chival(ch, x) == 1 or abs(chival(ch, x) - 1) < 1e-20
            for x in range(q)
            if gcd(x, q) == 1 and x % f == 1 % f
        ):
            return f
    return q


def primitive_table(ch, q: int, f: int) -> tuple[mp.mpc, ...]:
    """Values of chi* on 0..f-1."""
    vals = []
    for x in range(f):
        if gcd(x, f) > 1:
            vals.append(0j)
            continue
        y = next(y for y in range(x, x + f * q + 1, f) if gcd(y, q) == 1)
        vals.append(chival(ch, y))
    return tuple(vals)


def key(tab):
    return (
        len(tab),
        tuple((round(float(z.real), 8) + 0.0, round(float(z.imag), 8) + 0.0) for z in tab),
    )


def gauss(tab) -> mp.mpc:
    f = len(tab)
    return mp.fsum(mp.mpc(tab[a]) * e(mp.mpf(a) / f) for a in range(f))


def Lfun(s, tab, derivative: int = 0) -> mp.mpc:
    """L(s, psi) (derivative 0 or 1) via Hurwitz zeta; psi given by its value table mod f."""
    f = len(tab)
    terms = [(mp.mpc(tab[a]), mp.mpf(a) / f if a else mp.mpf(1)) for a in range(f) if tab[a] != 0]
    S0 = mp.fsum(c * mp.zeta(s, x) for c, x in terms)
    if not derivative:
        return mp.mpf(f) ** (-s) * S0
    S1 = mp.fsum(c * mp.zeta(s, x, 1) for c, x in terms)
    return mp.mpf(f) ** (-s) * (S1 - mp.log(f) * S0)


def decompose(n: int):
    """Return {primitive key: [tab, K, logcoeffs]} with I_n = sum K L'(-1,psi) + sum c_p log p (+ check)."""
    out: dict = {}
    logs: dict[int, mp.mpc] = {}
    byM: dict[int, list[int]] = {}
    for m, j in poles(n):
        byM.setdefault(m, []).append(j)
    for m, js in byM.items():
        q = 2 * m
        a = {j: a_formula(n, m, j) for j in js}
        phi = len(js)
        for ch in characters(q):
            alpha = mp.fsum(mp.conj(chival(ch, j)) * a[j] for j in js) / phi
            if abs(alpha) < 1e-20:
                continue
            f = conductor(ch, q)
            tab = primitive_table(ch, q, f)
            g = q // f
            sgn = tab[f - 1] if f > 1 else 1
            tau = gauss(tab) if f > 1 else mp.mpc(1)
            psi = tuple(mp.conj(z) for z in tab)  # L(s, conj chi*)
            divs = [d for d in range(1, g + 1) if g % d == 0]
            H = mp.fsum(
                mobius(g // d)
                * mp.mpc(tab[(g // d) % f] if f > 1 else 1)
                * mp.mpf(d) ** 2
                for d in divs
            )
            dH = {}  # H'(-1) = -sum mu chi d^2 log d  -> log coefficients per prime
            pre = -2 * alpha * sgn * tau
            k = key(psi)
            ent = out.setdefault(k, [psi, mp.mpc(0)])
            ent[1] += pre * H
            Lm1 = Lfun(-1, psi)
            for d in divs:
                w = (
                    mobius(g // d)
                    * mp.mpc(tab[(g // d) % f] if f > 1 else 1)
                    * mp.mpf(d) ** 2
                )
                for p, ex in factorint(d).items():
                    logs[p] = logs.get(p, mp.mpc(0)) + pre * Lm1 * (-w) * ex
    return out, logs


def I_from(out, logs) -> mp.mpc:
    return mp.fsum(K * Lfun(-1, tab, 1) for tab, K in out.values()) + mp.fsum(
        c * mp.log(p) for p, c in logs.items()
    )


def I_quad(n: int) -> mp.mpf:
    f = lambda x: mp.fprod(mp.tanh(k * x) for k in range(1, n + 1)) / x**2
    return mp.quad(f, [0, 0.5, 1, 2, 4, 8, 16, mp.inf])


def gauss_identity_check() -> float:
    err = 0.0
    for q in range(1, 41):
        for ch in characters(q):
            f = conductor(ch, q)
            tab = primitive_table(ch, q, f)
            g = q // f
            tau = gauss(tab) if f > 1 else 1
            for N in range(-3 * q, 3 * q + 1):
                lhs = mp.fsum(
                    chival(ch, j) * e(mp.mpf(-j * N) / q)
                    for j in range(q)
                    if gcd(j, q) == 1
                )
                rhs = (
                    (tab[f - 1] if f > 1 else 1)
                    * tau
                    * mp.fsum(
                        d
                        * mobius(g // d)
                        * (tab[(g // d) % f] if f > 1 else 1)
                        * mp.conj(tab[(N // d) % f] if f > 1 else 1)
                        for d in range(1, g + 1)
                        if g % d == 0 and N % d == 0
                    )
                )
                err = max(err, float(abs(lhs - rhs)))
    return err


if __name__ == "__main__":
    bad = False
    ge = gauss_identity_check()
    print(f"(a) Gauss-sum identity, q<=40: max err {ge:.1e}")
    bad |= ge > 1e-15
    asker = {
        3: 1.9095425048844384553,
        5: 1.7518763852341610453,
        7: 1.7203912772183856179,
        9: 1.7110140692970610143,
        11: 1.7076399598357368455,
    }
    for n in range(2, 12):
        out, logs = decompose(n)
        I = I_from(out, logs)
        Q = I_quad(n)
        d = abs(I - Q)
        print(
            f"(b) n={n:2d} char-form {mp.nstr(I.real, 22)} imag {float(abs(I.imag)):.0e} quad diff {float(d):.1e}"
            + (f" asker diff {abs(float(I.real) - asker[n]):.1e}" if n in asker else "")
        )
        bad |= d > 1e-18
    print("FAIL" if bad else "ALL PASS")
    sys.exit(int(bad))
