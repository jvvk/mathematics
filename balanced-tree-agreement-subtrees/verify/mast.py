"""Balanced-tree MAST: a recursive construction with exponent 5/11 < 1/2.

A balanced rooted binary tree of height H is stored as its leaf-label sequence
(length 2^H, left to right). Node (d, i) at depth d covers seq[i*2^(H-d):(i+1)*2^(H-d)].

Construction (one level, parameter k, base pair (A, B) on b leaves with mast m):
  p = 2^(2^k - k - 1) pendant subtrees S_i / T_j, each of height 2^k - 1 over
  "super-leaves" that are balanced blocks of size b.  Each S_i is perfectly
  partitioned into p caterpillars of c = 2^k super-leaves (Bordewich et al.,
  Cor. 4.4).  Cell (i, j) owns c blocks; S_i lays them along caterpillar j in
  order, T_j along caterpillar i in reverse order; blocks carry A in S, B in T.
  Claim: mast(S, T) <= 2 p m, on n = p^2 c b leaves.
"""

from __future__ import annotations

import itertools
import random
import sys

# ---------- caterpillar partition of a balanced tree (Lemma 4.3 / Cor. 4.4) ----------


def a054243(n: int) -> int:
    return 2 ** (n - 1 - (n - 1).bit_length())  # 2^floor(n - log2 n - 1) = 2^(n-1-ceil(log2 n))


def caterpillars(n: int, offset: int = 0) -> list[list[int]]:
    """Label-disjoint n-caterpillars in a balanced tree on 2^(n-1) leaves whose leaf
    positions are offset..offset+2^(n-1)-1.  Each caterpillar is listed deepest-first
    (l1, l2 cherry; last element attaches nearest the root)."""
    if n == 1:
        return [[offset]]
    half = 2 ** (n - 2)
    need = a054243(n)
    take = {
        offset: (need + 1) // 2,
        offset + half: need // 2,
    }  # caterpillars kept per half
    kept = {s: caterpillars(n - 1, s)[: take[s]] for s in take}
    out: list[list[int]] = []
    for side, other in ((offset, offset + half), (offset + half, offset)):
        used = {x for c in kept[other] for x in c}
        free = [x for x in range(other, other + half) if x not in used]
        assert len(free) >= len(kept[side]), (n, len(free), len(kept[side]))
        out += [c + [f] for c, f in zip(kept[side], free)]
    assert len(out) == need, (n, len(out), need)
    return out


# ---------- restriction / canonical form (for checking and brute force) ----------


def restrict(seq: list[int], ys: set[int]):
    """Canonical form of the balanced tree `seq` restricted to label set ys."""

    def go(lo: int, hi: int):
        if hi - lo == 1:
            return seq[lo] if seq[lo] in ys else None
        mid = (lo + hi) // 2
        l, r = go(lo, mid), go(mid, hi)
        if l is None:
            return r
        if r is None:
            return l
        return frozenset((l, r))

    return go(0, len(seq))


def caterpillar_form(order: list[int]):
    t = frozenset((order[0], order[1]))
    for x in order[2:]:
        t = frozenset((t, x))
    return t


# ---------- construction ----------


def build(levels: list[int]) -> tuple[list[int], list[int], int]:
    """Apply the construction for k in `levels`, innermost first, from the 1-leaf base.
    Returns (S, T, bound) where bound = product of 2p over levels."""
    A, B, bound = [0], [0], 1
    for k in levels:
        A, B, bound = level(A, B, bound, k)
    return A, B, bound


def level(A: list[int], B: list[int], m: int, k: int):
    b = len(A)
    c = 2**k
    h1 = c - k - 1
    p = 2**h1
    cats = caterpillars(c)  # positions in a tree of height c-1
    assert len(cats) == p and sorted(x for q in cats for x in q) == list(range(p * c))
    sup = p * c  # super-leaves per S_i
    S = [None] * (p * sup * b)
    T = [None] * (p * sup * b)
    for i in range(p):
        for j in range(p):
            for t in range(c):
                off = ((i * p + j) * c + t) * b
                s_pos = i * sup + cats[j][t]
                t_pos = j * sup + cats[i][c - 1 - t]
                S[s_pos * b : (s_pos + 1) * b] = [off + x for x in A]
                T[t_pos * b : (t_pos + 1) * b] = [off + x for x in B]
    assert sorted(S) == sorted(T) == list(range(len(S)))
    return S, T, 2 * p * m


# ---------- exact MAST for two balanced trees (sparse O(sum of overlaps) DP) ----------


def mast(S: list[int], T: list[int]) -> int:
    n = len(S)
    H = n.bit_length() - 1
    assert 2**H == n == len(T)
    posT = {x: i for i, x in enumerate(T)}
    tpos_of_S = [posT[x] for x in S]  # T-position of the label at S-position
    prev: dict[tuple[int, int, int], int] = {}  # values at S-depth d+1
    for d in range(H, -1, -1):
        cur: dict[tuple[int, int, int], int] = {}
        w = 2 ** (H - d)
        for i in range(2**d):
            tp = tpos_of_S[i * w : (i + 1) * w]
            for e in range(H, -1, -1):
                sh = H - e
                for j in sorted({q >> sh for q in tp}):
                    if d == H or e == H:
                        cur[(i, e, j)] = 1
                        continue
                    g = lambda dd, ii, ee, jj: (prev if dd == d + 1 else cur).get(
                        (ii, ee, jj), 0
                    )
                    u1, u2, v1, v2 = 2 * i, 2 * i + 1, 2 * j, 2 * j + 1
                    cur[(i, e, j)] = max(
                        g(d + 1, u1, e + 1, v1) + g(d + 1, u2, e + 1, v2),
                        g(d + 1, u1, e + 1, v2) + g(d + 1, u2, e + 1, v1),
                        g(d, i, e + 1, v1),
                        g(d, i, e + 1, v2),
                        g(d + 1, u1, e, j),
                        g(d + 1, u2, e, j),
                    )
        prev = cur
    return prev[(0, 0, 0)]


def mast_brute(S: list[int], T: list[int]) -> int:
    labels = list(S)
    for r in range(len(labels), 0, -1):
        for ys in itertools.combinations(labels, r):
            y = set(ys)
            if restrict(S, y) == restrict(T, y):
                return r
    return 0


# ---------- checks ----------


def check_caterpillars() -> None:
    for k in (1, 2, 3, 4):
        c = 2**k
        cats = caterpillars(c)
        seq = list(range(2 ** (c - 1)))
        assert sorted(x for q in cats for x in q) == seq, k  # perfect partition
        for q in cats:
            assert restrict(seq, set(q)) == caterpillar_form(q), (k, q)
    print("caterpillar partitions: perfect and correctly ordered for k=1..4")


def check_dp(trials: int = 300) -> None:
    rng = random.Random(1)
    for _ in range(trials):
        n = rng.choice([2, 4, 8, 16])
        S = list(range(n))
        T = list(range(n))
        rng.shuffle(S)
        rng.shuffle(T)
        assert mast(S, T) == mast_brute(S, T), (S, T)
    print(f"sparse DP agrees with brute force on {trials} random pairs (n<=16)")


def main() -> None:
    check_caterpillars()
    check_dp()
    for levels in ([2], [3], [2, 2], [2, 3], [3, 2], [2, 2, 2]):
        S, T, bound = build(levels)
        n = len(S)
        m = mast(S, T)
        print(f"levels={levels} n={n} mast={m} bound={bound} sqrt(n)={n**0.5:.1f}")
        assert m <= bound
    sys.stdout.flush()


if __name__ == "__main__":
    main()
