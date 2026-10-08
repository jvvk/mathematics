"""Independent recheck of the certificate proof for MO 479618 (shares no code with codex-2026-10-08/).

Part 1. The window identity: for a finitely supported row x, summing the local quantities I, O and the two
correction terms over all windows reproduces F(x), E[F(Tx) | x] and zero. Checked by exhaustive enumeration
of all coin outcomes on random short integer rows, with exact rational p.

Part 2. The local inequality G_p(a,b,c,d) >= 0 on the nonnegative orthant for p in [p0, 1]. The hyperplane
arrangement is derived here from the definition of G, extreme rays are recomputed by exact 3x3 minors, and
nonnegativity of each cubic in p is checked in the Bernstein basis on [p0, 1].

Run: python recheck.py   (standard library only; about a minute)
"""

from __future__ import annotations

import itertools
import random
from fractions import Fraction as Q
from math import comb

Vec = tuple[int, int, int, int]

CERTS = {
    # name: (t, u, v, lam, alpha (output correction), beta (input correction), p0)
    "main": (
        Q(1249, 2500),
        Q(3, 100),
        Q(557, 2500),
        Q(5001, 5000),
        Q(81, 2500),
        Q(999, 10000),
        Q(29, 125),
    ),
    "quarter": (Q(12, 25), Q(1, 32), Q(1, 5), Q(51, 50), Q(3, 100), Q(1, 10), Q(1, 4)),
}


# ---------- the process ----------
def step(x: list[int], coins: tuple[bool, ...]) -> list[int]:
    """Next row from zero-padded row x; coins[j] True = sum (heads). Output has len(x)+1 entries."""
    xp = [0] + x + [0]
    return [
        xp[j] + xp[j + 1] if coins[j] else abs(xp[j] - xp[j + 1])
        for j in range(len(x) + 1)
    ]


def functionals(x: list[int]) -> tuple[int, int, int, int]:
    """S, V, V2, W of the zero-padded row x."""
    xp = [0, 0] + x + [0, 0]
    S = sum(x)
    V = sum(abs(xp[j] - xp[j - 1]) for j in range(1, len(xp)))
    V2 = sum(abs(xp[j] - xp[j - 2]) for j in range(2, len(xp)))
    d = [abs(xp[j] - xp[j - 1]) for j in range(1, len(xp))]
    W = sum(abs(d[j] - d[j - 1]) for j in range(1, len(d)))
    return S, V, V2, W


def F(x: list[int], t: Q, u: Q, v: Q) -> Q:
    S, V, V2, W = functionals(x)
    return S + t * V + u * V2 + v * W


def check_row_triangle() -> None:
    """The zero-padded rule reproduces the question's triangle: edges are 1 whatever the coins."""
    x = [1]
    for _ in range(8):
        x = step(x, tuple(random.random() < 0.5 for _ in range(len(x) + 1)))
        assert x[0] == 1 and x[-1] == 1, x


# ---------- local quantities ----------
def local_I(a, b, c, d, t, u, v):
    return (
        Q(a + b + c + d, 4)
        + t * Q(abs(a - b) + abs(b - c) + abs(c - d), 3)
        + u * Q(abs(a - c) + abs(b - d), 2)
        + v * Q(abs(abs(a - b) - abs(b - c)) + abs(abs(b - c) - abs(c - d)), 2)
    )


def local_O(A, B, C, t, u, v):
    return (
        Q(A + B + C, 3)
        + t * Q(abs(A - B) + abs(B - C), 2)
        + u * abs(A - C)
        + v * abs(abs(A - B) - abs(B - C))
    )


def upd(x, y, heads):
    return x + y if heads else abs(x - y)


def G_poly(a, b, c, d, cert) -> list[Q]:
    """G_p(a,b,c,d) as power-basis coefficients [g0, g1, g2, g3] in p (a, b, c, d may be Fractions)."""
    t, u, v, lam, al, be, _ = cert
    poly = [Q(0)] * 4
    for h in itertools.product((True, False), repeat=3):
        A, B, C = upd(a, b, h[0]), upd(b, c, h[1]), upd(c, d, h[2])
        val = local_O(A, B, C, t, u, v) - al * (A + C - 2 * B)
        k = sum(h)  # weight p^k (1-p)^(3-k), expanded
        for i in range(3 - k + 1):
            poly[k + i] += val * comb(3 - k, i) * (-1) ** i
    poly[0] += -lam * local_I(a, b, c, d, t, u, v) + be * (a + d - b - c)
    return poly


def check_window_identity(trials: int = 40) -> None:
    rng = random.Random(479618)
    for name, cert in CERTS.items():
        t, u, v, lam, al, be, _ = cert
        for _ in range(trials):
            n = rng.randint(1, 5)
            x = [rng.randint(0, 9) for _ in range(n)]
            p = Q(rng.randint(1, 99), 100)
            # exact E[F(Tx)] by enumerating all 2^(n+1) coin vectors
            EF = Q(0)
            for coins in itertools.product((True, False), repeat=n + 1):
                w = p ** sum(coins) * (1 - p) ** (n + 1 - sum(coins))
                EF += w * F(step(x, coins), t, u, v)
            # sum of local quantities over all windows (a,b,c,d) = (x_{j-2}, x_{j-1}, x_j, x_{j+1})
            xp = [0] * 4 + x + [0] * 4
            sumI = sumG = Q(0)
            for j in range(2, len(xp) - 1):
                a, b, c, d = xp[j - 2], xp[j - 1], xp[j], xp[j + 1]
                sumI += local_I(a, b, c, d, t, u, v)
                g = G_poly(a, b, c, d, cert)
                sumG += sum(g[i] * p**i for i in range(4))
            assert sumI == F(x, t, u, v), (x, sumI, F(x, t, u, v))
            # summing G over windows must give E[F(Tx)] - lam F(x) (corrections telescope to zero)
            assert sumG == EF - lam * F(x, t, u, v), (name, x, p)
        print(
            f"window identity [{name}]: {trials} random rows exact, all coin outcomes enumerated"
        )


# ---------- the arrangement ----------
def normalise(h: Vec) -> Vec | None:
    if all(c == 0 for c in h):
        return None
    from math import gcd

    g = 0
    for c in h:
        g = gcd(g, abs(c))
    h = tuple(c // g for c in h)
    first = next(c for c in h if c != 0)
    return h if first > 0 else tuple(-c for c in h)


def arrangement() -> list[Vec]:
    """Every hyperplane across which some absolute value inside G changes sign (over-refinement is harmless)."""
    e = [(1, 0, 0, 0), (0, 1, 0, 0), (0, 0, 1, 0), (0, 0, 0, 1)]
    add = lambda *vs: tuple(sum(c) for c in zip(*vs))
    sc = lambda k, w: tuple(k * c for c in w)
    a, b, c, d = e
    H = set(e)
    # input terms: |a-b|, |b-c|, |c-d|, |a-c|, |b-d|, and ||a-b|-|b-c|| changes sign on (a-c)(a-2b+c)=0
    for w in [
        add(a, sc(-1, b)),
        add(b, sc(-1, c)),
        add(c, sc(-1, d)),
        add(a, sc(-1, c)),
        add(b, sc(-1, d)),
        add(a, sc(-2, b), c),
        add(b, sc(-2, c), d),
    ]:
        H.add(normalise(w))
    # output: A in {a+b, +-(a-b)} etc.; |A-B|, |B-C|, |A-C|, and ||A-B|-|B-C|| via (A-C)(A-2B+C)
    forms = lambda x, y: [add(x, y), add(x, sc(-1, y)), add(y, sc(-1, x))]
    for A, B, C in itertools.product(forms(a, b), forms(b, c), forms(c, d)):
        for w in [
            add(A, sc(-1, B)),
            add(B, sc(-1, C)),
            add(A, sc(-1, C)),
            add(A, sc(-2, B), C),
        ]:
            n = normalise(w)
            if n:
                H.add(n)
    return sorted(H)


def kernel(r1: Vec, r2: Vec, r3: Vec) -> Vec | None:
    """Generator of the null space of the 3x4 matrix (rows r1..r3) by signed 3x3 minors; None if rank < 3."""
    M = [r1, r2, r3]
    out = []
    for k in range(4):
        cols = [j for j in range(4) if j != k]
        m = [[M[i][j] for j in cols] for i in range(3)]
        det = (
            m[0][0] * (m[1][1] * m[2][2] - m[1][2] * m[2][1])
            - m[0][1] * (m[1][0] * m[2][2] - m[1][2] * m[2][0])
            + m[0][2] * (m[1][0] * m[2][1] - m[1][1] * m[2][0])
        )
        out.append((-1) ** k * det)
    return normalise(tuple(out)) if any(out) else None


def orthant_rays(H: list[Vec]) -> list[Vec]:
    rays = set()
    for h1, h2, h3 in itertools.combinations(H, 3):
        k = kernel(h1, h2, h3)
        if k is None:
            continue
        for s in (k, tuple(-c for c in k)):
            if all(c >= 0 for c in s):
                rays.add(s)
    return sorted(rays)


def bernstein_on(poly: list[Q], p0: Q) -> list[Q]:
    """Cubic Bernstein coefficients on q in [0,1] of poly(p0 + (1-p0) q)."""
    s = 1 - p0
    # power coefficients in q
    cq = [Q(0)] * 4
    for i, g in enumerate(poly):
        for j in range(i + 1):
            cq[j] += g * comb(i, j) * p0 ** (i - j) * s**j
    # power -> Bernstein (degree 3): b_k = sum_{j<=k} C(k,j)/C(3,j) cq_j
    return [
        sum(Q(comb(k, j), comb(3, j)) * cq[j] for j in range(k + 1)) for k in range(4)
    ]


def check_certificate(name: str, cert) -> None:
    H = arrangement()
    R = orthant_rays(H)
    p0 = cert[6]
    coeffs = [b for r in R for b in bernstein_on(G_poly(*r, cert), p0)]
    m = min(coeffs)
    assert m > 0, (name, m)
    print(
        f"certificate [{name}]: {len(H)} hyperplanes, {len(R)} orthant rays, {len(coeffs)} Bernstein coefficients,"
        f" min {m}"
    )


def check_mutants() -> None:
    """The checker must reject false variants."""
    t, u, v, lam, al, be, p0 = CERTS["main"]
    bad = {
        "lambda 5003/5000": (t, u, v, Q(5003, 5000), al, be, p0),
        "p0 = 0.2": (t, u, v, lam, al, be, Q(1, 5)),
        "no W term": (t, u, Q(0), lam, al, be, p0),
        "no corrections": (t, u, v, lam, Q(0), Q(0), p0),
    }
    R = orthant_rays(arrangement())
    for label, cert in bad.items():
        m = min(b for r in R for b in bernstein_on(G_poly(*r, cert), cert[6]))
        assert m < 0, label
        print(f"mutant rejected: {label} (min coefficient {float(m):.3g})")


if __name__ == "__main__":
    random.seed(1)
    check_row_triangle()
    check_window_identity()
    for name, cert in CERTS.items():
        check_certificate(name, cert)
    check_mutants()
    print("ALL PASS")
