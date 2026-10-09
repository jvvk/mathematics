"""MO 501839: sign-reversing involution proving N_{n,k}(-1) = #symmetric Dyck paths of semilength n with k+1 peaks.

Encoding. A Dyck path with k valleys has up-run partial sums U_1<..<U_k and down-run partial sums D_1<..<D_k in
[n-1], with U_j >= D_j; valley j sits at position U_j + D_j, so maj = sum(U) + sum(D). Write a word of length n-1:
letter at x is (x in U, x in D): 'u' = (0,1), 'd' = (1,0), 'a' = (0,0), 'b' = (1,1). U_j >= D_j for all j says every
prefix has #u >= #d: a Motzkin path (u up, d down, a and b level). k = #u + #b, sign = prod over u,d at x of (-1)^x.

Involution on blocks (1,2), (3,4), ...; the last letter is unpaired when n-1 is odd. Partners: a block with exactly
one level letter <-> its swap; ud <-> ba; du <-> ab at height >= 1 (height before the block). Replace the first
block that has a partner.
Fixed points: blocks uu, dd, aa, bb, and ab at height 0; sign +1.
Bijection to symmetric paths: halve blocks (uu->U, dd->D, aa->a, bb->b, ab->c at height 0), turn each c into U
(the last departures from each level), giving a Motzkin prefix of length floor((n-1)/2); append the unpaired letter
if any, then the mirror image. That word is reversal-symmetric, which is the encoding of a symmetric Dyck path.
"""

from __future__ import annotations

import sys
from collections import Counter

Word = str


def dyck(n: int):
    def rec(path: list[int], up: int, down: int):
        if up == n and down == n:
            yield tuple(path)
            return
        if up < n:
            path.append(1)
            yield from rec(path, up + 1, down)
            path.pop()
        if down < up:
            path.append(-1)
            yield from rec(path, up, down + 1)
            path.pop()

    yield from rec([], 0, 0)


def encode(P: tuple[int, ...]) -> Word:
    n = len(P) // 2
    U: set[int] = set()
    D: set[int] = set()
    ups = downs = 0
    for i in range(len(P) - 1):
        ups += P[i] == 1
        downs += P[i] == -1
        if P[i] == -1 and P[i + 1] == 1:
            U.add(ups)
            D.add(downs)
    return "".join(
        {(0, 1): "u", (1, 0): "d", (0, 0): "a", (1, 1): "b"}[(x in U, x in D)]
        for x in range(1, n)
    )


def decode(w: Word) -> tuple[int, ...]:
    n = len(w) + 1
    U = [x for x in range(1, n) if w[x - 1] in "db"]
    D = [x for x in range(1, n) if w[x - 1] in "ub"]
    ur = [b - a for a, b in zip([0] + U, U + [n])]
    dr = [b - a for a, b in zip([0] + D, D + [n])]
    return tuple(s for r, t in zip(ur, dr) for s in [1] * r + [-1] * t)


def sign(w: Word) -> int:
    return (-1) ** sum(x for x, c in enumerate(w, 1) if c in "ud")


def peaks(w: Word) -> int:
    return w.count("u") + w.count("b") + 1


def is_motzkin(w: Word) -> bool:
    h = 0
    for c in w:
        h += (c == "u") - (c == "d")
        if h < 0:
            return False
    return h == 0


PARTNER = {"ua": "au", "au": "ua", "ub": "bu", "bu": "ub", "da": "ad", "ad": "da", "db": "bd", "bd": "db",
           "ud": "ba", "ba": "ud"}
PARTNER_HIGH = {"du": "ab", "ab": "du"}  # only at height >= 1


def iota(w: Word) -> Word:
    """Replace the first block that has a partner."""
    h = 0
    for i in range(0, len(w) - 1, 2):
        B = w[i:i + 2]
        if B in PARTNER:
            return w[:i] + PARTNER[B] + w[i + 2:]
        if B in PARTNER_HIGH and h >= 1:
            return w[:i] + PARTNER_HIGH[B] + w[i + 2:]
        h += B.count("u") - B.count("d")
    return w


def to_symmetric(w: Word) -> Word:
    """Fixed point of iota -> encoding word of a symmetric Dyck path."""
    half = []
    for i in range(0, len(w) - 1, 2):
        half.append(
            {"uu": "u", "dd": "d", "aa": "a", "bb": "b", "ab": "c"}[w[i : i + 2]]
        )
    # each c (at height 0) becomes an up step: these are the last departures from levels 0, 1, 2, ...
    half_w = "".join("u" if c == "c" else c for c in half)
    mid = w[-1] if len(w) % 2 else ""
    mirror = half_w[::-1].translate(str.maketrans("ud", "du"))
    return half_w + mid + mirror


def is_symmetric(P: tuple[int, ...]) -> bool:
    return tuple(-s for s in P[::-1]) == P


def check(n: int) -> tuple[int, Counter, Counter]:
    words = [encode(P) for P in dyck(n)]
    assert all(decode(w) == P for w, P in zip(words, dyck(n))), (
        "encoding not invertible"
    )
    assert all(is_motzkin(w) for w in words)
    wset = set(words)
    fixed: list[Word] = []
    for w in words:
        v = iota(w)
        assert v in wset, f"iota leaves the set: {w} -> {v}"
        assert iota(v) == w, f"not an involution: {w} -> {v} -> {iota(v)}"
        assert peaks(v) == peaks(w), f"peaks changed: {w} -> {v}"
        if v == w:
            fixed.append(w)
            assert sign(w) == 1, f"negative fixed point {w}"
        else:
            assert sign(v) == -sign(w), f"sign not reversed: {w} -> {v}"
    images = [to_symmetric(w) for w in fixed]
    assert len(set(images)) == len(images), "bijection not injective"
    sym = {encode(P) for P in dyck(n) if is_symmetric(P)}
    assert set(images) == sym, "image is not the symmetric set"
    assert all(peaks(to_symmetric(w)) == peaks(w) for w in fixed), (
        "bijection changes peaks"
    )
    signed = Counter()
    symc = Counter()
    for w in words:
        signed[peaks(w)] += sign(w)
    for P in dyck(n):
        if is_symmetric(P):
            symc[peaks(encode(P))] += 1
    assert signed == +symc, "signed sum != symmetric count"
    return len(fixed), signed, symc


if __name__ == "__main__":
    N = int(sys.argv[1]) if len(sys.argv) > 1 else 10
    for n in range(1, N + 1):
        f, signed, symc = check(n)
        print(f"n={n}: fixed={f} by peaks {dict(sorted(symc.items()))} OK")
