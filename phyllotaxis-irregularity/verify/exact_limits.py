"""Review point 2: the candidate tables of the limiting tilings in EXACT rational arithmetic.

certify_limits.py reports degeneracies as interval "TIE"s, which do not prove equality. Here every limiting
front is a word in the vectors of a triangular lattice, written in the rational model of modulus N (a point
(X, Y) stands for (X/sqrtN, sqrt3 Y/sqrtN), squared distances are (dX^2 + 3 dY^2)/N, rotation by 60 degrees is
rational). Every candidate position is then a rational point: pairs at distance 1 have apex P + rot60(R - P),
pairs at distance sqrt3 have apex P + (R - P) e^{i30}/sqrt3, pairs at distance 2 have the midpoint, and
farther pairs have none. Validity and ties are exact identities.

Words: K0 at the placement of the pentagon (N = 19, Lemma K0) and the four words of the (2,2) phase
(N = 7, Lemma alternation). For each: the locations in order of height, the candidates at each location with
the disks they touch, and the exact height gap from the lowest location to the next valid one.
"""

from __future__ import annotations

from fractions import Fraction as Fr
from math import sqrt

Pt = tuple[Fr, Fr]


def rot(v: Pt, s: int) -> Pt:
    x, y = v
    return ((x - 3 * y) / 2, (x + y) / 2) if s > 0 else ((x + 3 * y) / 2, (y - x) / 2)


def q(p: Pt, r: Pt) -> Fr:
    return (r[0] - p[0]) ** 2 + 3 * (r[1] - p[1]) ** 2


def apex(p: Pt, r: Pt, N: int):
    d = (r[0] - p[0], r[1] - p[1])
    qq = q(p, r)
    if qq == N:
        w = rot(d, 1)
        return (p[0] + w[0], p[1] + w[1])
    if qq == 3 * N:
        return (p[0] + (d[0] - d[1]) / 2, p[1] + d[0] / 6 + d[1] / 2)
    if qq == 4 * N:
        return ((p[0] + r[0]) / 2, (p[1] + r[1]) / 2)
    if qq > 4 * N:
        return None
    raise ValueError(f"non-lattice pair, q = {qq}")


def above(Q: Pt, poly: list[Pt]) -> bool:
    """Q lies strictly above the front polyline (the stack fills the region below it)."""
    for (x1, y1), (x2, y2) in zip(poly, poly[1:]):
        if x1 <= Q[0] <= x2:
            return Q[1] > y1 + (y2 - y1) * (Q[0] - x1) / (x2 - x1)
    raise ValueError("outside the polyline")


def table(name: str, vecs: list[Pt], labels: list[str], N: int):
    pts = [(Fr(0), Fr(0))]
    for v in vecs[:-1]:
        pts.append((pts[-1][0] + v[0], pts[-1][1] + v[1]))
    L = sum(v[0] for v in vecs)
    assert sum(v[1] for v in vecs) == 0
    n = len(pts)
    poly = sorted((pts[k][0] + s * L, pts[k][1]) for k in range(n) for s in (-1, 0, 1, 2))
    disks = [(pts[k][0] + s * L, pts[k][1], k) for k in range(n) for s in (-1, 0, 1)]
    locs: dict[tuple[Fr, Fr], list[str]] = {}
    for a in range(n):
        for gap in range(n - 1):
            b = a + gap + 1
            R = pts[b % n] if b < n else (pts[b % n][0] + L, pts[b % n][1])
            if R[0] <= pts[a][0]:
                continue
            Q = apex(pts[a], R, N)
            if Q is None:
                continue
            for p, r in ((pts[a], R),):
                assert q(p, Q) == N and q(Q, r) == N
            overl = [k for (x, y, k) in disks if q((x, y), Q) < N]
            if overl or not above(Q, poly):
                continue
            touch = sorted(
                {
                    labels[k] if k < len(labels) else str(k)
                    for (x, y, k) in disks
                    if q((x, y), Q) == N
                }
            )
            kind = "TRP"[gap] if gap < 3 else f"G{gap}"
            key = (Q[0] % L, Q[1])
            locs.setdefault(key, []).append(
                f"{kind}({labels[a]}..{labels[(b - 1) % n]}) touching {','.join(touch)}"
            )
    order = sorted(locs, key=lambda k: k[1])
    print(f"== {name}  (N = {N}, period X = {L})")
    y0 = order[0][1]
    for key in order[:3]:
        dy = key[1] - y0
        print(
            f"   Y = {key[1]} (above lowest by dY = {dy}, height {float(dy) * sqrt(3 / N):.6f}): "
            + "; ".join(locs[key])
        )
    gap = order[1][1] - y0
    return gap, (order[2][1] - y0 if len(order) > 2 else None)


if __name__ == "__main__":
    # K0 (N = 19): D = (4,-1), U = rot(D,+1) = (7/2, 3/2), S = rot(D,-1) = (1/2, -5/2); word U S U S U U D
    D = (Fr(4), Fr(-1))
    U, S = rot(D, 1), rot(D, -1)
    assert U == (Fr(7, 2), Fr(3, 2)) and S == (Fr(1, 2), Fr(-5, 2))
    names = ["z0", "z1", "z2", "P0", "P1", "P2", "P3"]
    g, g2 = table(
        "K0 at the pentagon (word U S U S U U D)", [U, S, U, S, U, U, D], names, 19
    )
    assert g == Fr(1, 2) and g2 >= 1, (g, g2)  # T sqrt(3/76) higher, all else >= 2 sqrt(3/76)
    # (2,2) phase (N = 7): Ua = (5/2, 1/2), D = Ub/- = (2, -1), Ub/+ = rot(Ua, +1) = (1/2, 3/2)
    Ua, D1 = (Fr(5, 2), Fr(1, 2)), (Fr(2), Fr(-1))
    Up = rot(Ua, 1)
    assert Up == (Fr(1, 2), Fr(3, 2)) and rot(Ua, -1) == D1
    words = [
        ("(2,2) word 1: Ua D Ub/+ Ub/-", [Ua, D1, Up, D1], ["Ua", "D", "Ub/+", "Ub/-"]),
        ("(2,2) word 2: Ua Ub/- D Ub/+", [Ua, D1, D1, Up], ["Ua", "Ub/-", "D", "Ub/+"]),
        ("(2,2) word 3: Ua Ub/- Ub/+ D", [Ua, D1, Up, D1], ["Ua", "Ub/-", "Ub/+", "D"]),
        ("(2,2) word 4: Ua D Ub/- Ub/+", [Ua, D1, D1, Up], ["Ua", "D", "Ub/-", "Ub/+"]),
    ]
    for name, vecs, labs in words:
        g, _ = table(name, vecs, labs, 7)
        assert g == Fr(1, 2), g  # next location sqrt(3/28) higher
    print("all gaps exact: K0 dY = 1/2 (sqrt(3/76)), (2,2) words dY = 1/2 (sqrt(3/28))")
