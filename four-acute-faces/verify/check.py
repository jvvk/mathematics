"""Exact checks of every finite claim in paper.tex (Four acute faces).

Points are rational unit vectors from inverse stereographic projection, so all
arithmetic is exact. MUTANT=1 moves the threshold from 4 to 3; MUTANT=2 changes
the count to N = 4 - 2m + 2J. Each mutant must make the script fail.
"""

import os
import random
from fractions import Fraction as F
from itertools import combinations, product

MUTANT = os.environ.get("MUTANT", "0")
Vec = tuple[F, F, F]


def dot(u: Vec, v: Vec) -> F:
    return sum(a * b for a, b in zip(u, v))


def add(*vs: Vec) -> Vec:
    return tuple(sum(c) for c in zip(*vs))


def neg(u: Vec) -> Vec:
    return tuple(-a for a in u)


def sc(k: int, u: Vec) -> Vec:
    return tuple(k * a for a in u)


def unit(p: F, q: F) -> Vec:
    d = p * p + q * q + 1
    return (2 * p / d, 2 * q / d, (p * p + q * q - 1) / d)


def angles_acute(tri: list[Vec]) -> bool:
    for i in range(3):
        z, x, y = tri[i], tri[(i + 1) % 3], tri[(i + 2) % 3]
        if dot(add(x, neg(z)), add(y, neg(z))) <= 0:
            return False
    return True


# Eight classes: sigma with sigma[0] = +1 represents {sigma, -sigma}.
CLASSES = [(1,) + s for s in product((1, -1), repeat=3)]
EVEN = [s for s in CLASSES if s.count(-1) % 2 == 0]
ODD = [s for s in CLASSES if s.count(-1) % 2 == 1]


def canon(s: tuple[int, ...]) -> tuple[int, ...]:
    return s if s[0] == 1 else tuple(-x for x in s)


def common_face(e: tuple[int, ...], o: tuple[int, ...]) -> tuple[int, tuple[int, ...]]:
    """Missing index and the signed face shared by e and o (Lemma 2)."""
    for oo in (o, tuple(-x for x in o)):
        diff = [i for i in range(4) if e[i] != oo[i]]
        if len(diff) == 1:
            return diff[0], e
    raise AssertionError("even and odd share no face")


def check(pts: list[Vec]) -> tuple[int, int, int]:
    signed = lambda s: [sc(s[i], pts[i]) for i in range(4)]
    w = {s: dot(add(*signed(s)), add(*signed(s))) for s in CLASSES}
    # Lemma 2: same parity share no face.
    for s, t in combinations(CLASSES, 2):
        if (s in EVEN) == (t in EVEN):
            assert all(
                sum(a != b for a, b in zip(s, tt)) == 2
                for tt in (t, tuple(-x for x in t))
            )
    short: set[tuple[tuple[int, ...], tuple[int, ...]]] = set()
    sums_seen: set[tuple[int, tuple[int, ...]]] = set()
    for e, o in product(EVEN, ODD):
        miss, sig = common_face(e, o)
        L = add(*[sc(sig[i], pts[i]) for i in range(4) if i != miss])
        key = (miss, canon(tuple(sig[i] if i != miss else 1 for i in range(4))))
        sums_seen.add(key)
        # Lemma 4 identity and threshold.
        assert w[e] + w[o] == 2 * dot(L, L) + 2
        thr = 3 if MUTANT == "1" else 4
        assert (dot(L, L) < 1) == (w[e] + w[o] < thr)
        if dot(L, L) < 1:
            short.add((e, o))
    assert len(sums_seen) == 16  # every triangle is exactly one cell
    # Lemma 3 criterion: N from angles equals lines containing every short cell.
    N_angles = 0
    for s in CLASSES:
        v = signed(s)
        if all(angles_acute([v[i] for i in range(4) if i != l]) for l in range(4)):
            N_angles += 1
    lines = [("r", e) for e in EVEN] + [("c", o) for o in ODD]
    on = lambda cell, ln: cell[0] == ln[1] if ln[0] == "r" else cell[1] == ln[1]
    N_lines = sum(all(on(c, ln) for c in short) for ln in lines)
    assert N_angles == N_lines
    # Lemma 5.
    m = len(short)
    assert 1 <= m <= 4
    assert all(sum(on(c, ln) for c in short) <= 3 for ln in lines)
    # Staircase: sorted by w, short cells are a Young diagram.
    rows = sorted(EVEN, key=lambda s: w[s])
    cols = sorted(ODD, key=lambda s: w[s])
    for i, j in product(range(4), range(4)):
        if (rows[i], cols[j]) in short:
            assert all(
                (rows[a], cols[b]) in short for a in range(i + 1) for b in range(j + 1)
            )
    J = sum(
        sum(on(c, ln) for c in short) * (sum(on(c, ln) for c in short) - 1) // 2
        for ln in lines
    )
    k = 2 if MUTANT == "2" else 1
    assert N_lines == 4 - 2 * m + k * J
    return N_lines, m, J


def main() -> None:
    # Example of Figure 1.
    x, y, z = (F(1), F(0), F(0)), (F(0), F(1), F(0)), (F(3, 5), F(4, 5), F(0))
    assert dot(add(x, neg(z)), add(y, neg(z))) == F(-2, 5)
    s = add(x, y, neg(z))
    assert dot(s, s) == F(1, 5)
    assert angles_acute([x, y, neg(z)]) and not angles_acute([x, y, z])
    # Dimension remark: orthonormal vectors in R^4 give squared sums 3.
    e4 = [tuple(F(int(i == j)) for j in range(4)) for i in range(4)]
    for tri in combinations(range(4), 3):
        for sg in product((1, -1), repeat=3):
            v = add(*[sc(sg[t], e4[tri[t]]) for t in range(3)])
            assert dot(v, v) == 3
    # Integrals: t^2 uniform on [0,1]; E t = 2/3, E t^2 = 1/2.
    Et, Et2 = F(2, 3), F(1, 2)
    alpha, gamma = (1 - Et) / 2, (1 - 2 * Et + Et2) / 4
    assert (alpha, gamma) == (F(1, 6), F(1, 24))
    EN = 4 - 2 * 16 * alpha + 48 * gamma
    assert EN == F(2, 3) and EN / 8 == F(1, 12)
    assert 1 - 3 * alpha == F(1, 2)
    # Random exact configurations.
    rng = random.Random(1)
    shapes: dict[tuple[int, int, int], int] = {}
    for _ in range(600):
        pts = [
            unit(
                F(rng.randint(-40, 40), rng.randint(1, 13)),
                F(rng.randint(-40, 40), rng.randint(1, 13)),
            )
            for _ in range(4)
        ]
        key = check(pts)
        shapes[key] = shapes.get(key, 0) + 1
    print(
        "(N, m, J) counts over 600 exact configurations:", dict(sorted(shapes.items()))
    )
    print("all checks passed")


if __name__ == "__main__":
    main()
