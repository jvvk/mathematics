"""Exact relations among angles with rational cosine (after Conway, Radin and Sadun 1999).

An angle theta with cos theta = c/q rational and sin theta = s sqrt(a)/q (a squarefree) satisfies
e^{i theta} = beta/conj(beta) * unit with beta = q + c + i s sqrt(a)?  We use the form needed here:

  rim angle alpha_d (sin(alpha_d/2) = 1/sqrt d):  d - 1 = s^2 a,  alpha_d = pi + 2 arg(1 - s sqrt(-a)).

In K = Q(sqrt(-a)), a sum of m_k arg(beta_k) is a rational multiple of pi iff gamma = prod beta_k^{m_k}
has gamma/conj(gamma) a root of unity, iff for every split prime p the valuations at the two primes above p
agree: sum_k m_k (v_P(beta_k) - v_Pbar(beta_k)) = 0. For beta = x + y sqrt(-a) with gcd(x, y) = 1 the whole
p-part p^e of the norm x^2 + a y^2 lies in one of P, Pbar, so the difference is +-e, the sign fixed by whether
x + y r = 0 mod p^e for the canonical square root r of -a.  Then 2 arg(gamma) is a multiple of 2 pi / w,
w = #roots of unity in K (4 for a = 1, 6 for a = 3, else 2).
"""
from __future__ import annotations

from collections import defaultdict


def factor(n: int) -> dict[int, int]:
    f, p = {}, 2
    while p * p <= n:
        while n % p == 0:
            f[p] = f.get(p, 0) + 1
            n //= p
        p += 1
    if n > 1:
        f[n] = f.get(n, 0) + 1
    return f


def squarefree_split(m: int) -> tuple[int, int]:
    """m = s^2 a with a squarefree; returns (a, s)."""
    a, s = 1, 1
    for p, e in factor(m).items():
        s *= p ** (e // 2)
        if e % 2:
            a *= p
    return a, s


def sqrt_mod_pk(t: int, p: int, k: int) -> int | None:
    """A square root of t modulo p^k (p odd, p not dividing t), canonical: the smaller root mod p, lifted."""
    r0 = None
    for r in range(p):
        if (r * r - t) % p == 0:
            r0 = r
            break
    if r0 is None:
        return None
    r, pk = r0, p
    for _ in range(1, k):
        pk2 = pk * p
        # Hensel: r <- r - (r^2 - t) / (2 r)  mod p^{k}
        r = (r - (r * r - t) * pow(2 * r, -1, pk2)) % pk2
        pk = pk2
    return r


def sqrt_mod_2k(t: int, k: int) -> int:
    """The square root of t = 1 mod 8 modulo 2^k that is 1 mod 4 (canonical 2-adic root)."""
    r = 1
    for j in range(3, k + 1):  # r^2 = t mod 2^j
        if (r * r - t) % (2 ** j) != 0:
            r += 2 ** (j - 2)
    r %= 2 ** k
    if r % 4 != 1:
        r = (-r) % 2 ** k
    assert (r * r - t) % (2 ** k) == 0
    return r


def vp(n: int, p: int, cap: int) -> int:
    """min(v_p(n), cap)."""
    if n == 0:
        return cap
    v = 0
    while v < cap and n % p == 0:
        n //= p
        v += 1
    return v


def valuation_vector(a: int, x: int, y: int) -> dict[int, int]:
    """{split prime p: v_P(beta) - v_Pbar(beta)} for beta = x + y sqrt(-a), a squarefree, (x, y) != 0.

    For a split prime p, O_K tensor Z_p = Z_p x Z_p via sqrt(-a) -> (rho, -rho) with rho^2 = -a in Z_p, so
    v_P(beta) = v_p(x + y rho) and v_Pbar(beta) = v_p(x - y rho); they add up to e = v_p(norm), so rho is
    only needed modulo p^(e+1). Ramified and inert primes give equal valuations and are skipped."""
    N = x * x + a * y * y
    out = {}
    for p, e in factor(N).items():
        if p == 2:
            if (-a) % 8 != 1:
                continue
            rho = sqrt_mod_2k(-a % 2 ** (e + 3), e + 3)
        else:
            if a % p == 0:
                continue
            rho = sqrt_mod_pk(-a % p ** (e + 1), p, e + 1)
            if rho is None:
                continue  # inert
        v1, v2 = vp(x + y * rho, p, e), vp(x - y * rho, p, e)
        assert v1 + v2 == e, (a, x, y, p, e, v1, v2)
        if v1 != v2:
            out[p] = v1 - v2
    return out


def roots_of_unity(a: int) -> int:
    return {1: 4, 3: 6}.get(a, 2)


def rim_data(d: int) -> tuple[int, dict[int, int]]:
    """Class a (0 for d = 1, where alpha_1 = pi) and valuation vector of beta = 1 - s sqrt(-a)."""
    if d == 1:
        return 0, {}
    a, s = squarefree_split(d - 1)
    return a, valuation_vector(a, 1, -s)


def is_relation(vecs: list[dict[int, int]], mults: list[int]) -> bool:
    tot: dict[int, int] = defaultdict(int)
    for v, m in zip(vecs, mults):
        for p, e in v.items():
            tot[p] += m * e
    return all(t == 0 for t in tot.values())
