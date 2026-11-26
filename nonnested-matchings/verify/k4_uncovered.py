"""Theorem 3, Computation 1: uncovered 16-edge families with both centre gaps at most 3.

1. Enumerate, by depth-first search over all short edges (no structural assumption), every set of 16 short edges on
   [m] that uses vertices 1 and m, has no non-nested 4-matching and no 3 vertices meeting all of its edges, for
   m = 8..13 (by Lemma 8 a family with both gaps <= 3 lies in [c1-3, c3+3], so m <= 13).
2. Keep those whose centres (the 2nd, 4th, ... vertices of each path of length-1 edges) have both gaps <= 3: there
   must be exactly 16.
3. Place each with A, B = 0..7 free vertices on the left and right; reverse if needed so that the first centre c
   carries all six short edges at c; check that the window [c-1, c+2] is good: for every p < q < r in cyclic order
   after c+2, S together with the star chords (4) of length >= 4 contains a non-nested 4-matching.

Usage: python3 k4_uncovered.py [--quick]   (quick: margins 0..2; full: 0..7, a few minutes)
"""

import itertools
import sys

if not __debug__:
    sys.exit("refusing to run under python -O: the checks are assertions")

MAXM = 2 if "--quick" in sys.argv else 7


def nested(e, f):
    return (e[0] < f[0] and f[1] < e[1]) or (f[0] < e[0] and e[1] < f[1])


def compat(e, f):
    return not set(e) & set(f) and not nested(e, f)


def has_nnk(edges, k, M=()):
    if k == 0:
        return True
    for j, e in enumerate(edges):
        if all(compat(e, f) for f in M) and has_nnk(edges[j + 1 :], k - 1, M + (e,)):
            return True
    return False


def covered3(S):
    V = sorted({v for e in S for v in e})
    return any(all(set(e) & set(T) for e in S) for T in itertools.combinations(V, 3))


def enumerate_span(m):
    E = sorted((a, a + d) for d in (1, 2, 3) for a in range(1, m - d + 1))
    out = []

    def dfs(i, S, cnt):
        if len(S) == 16:
            if (
                min(a for a, _ in S) == 1
                and max(b for _, b in S) == m
                and not covered3(S)
            ):
                out.append(tuple(S))
            return
        if len(S) + len(E) - i < 16:
            return
        for j in range(i, len(E)):
            e = E[j]
            d = e[1] - e[0]
            if cnt[d] >= 6:
                continue
            rest = [f for f in S if compat(e, f)]
            if has_nnk(rest, 3):
                continue
            cnt[d] += 1
            S.append(e)
            dfs(j + 1, S, cnt)
            S.pop()
            cnt[d] -= 1

    dfs(0, [], {1: 0, 2: 0, 3: 0})
    return out


def centres(S):
    U = {e for e in S if e[1] - e[0] == 1}
    cs, seen = [], set()
    for a, _ in sorted(U):
        if a in seen:
            continue
        path = [a]
        while (path[-1], path[-1] + 1) in U:
            path.append(path[-1] + 1)
        seen.update(path)
        cs += path[1::2]
    return cs


def full_star(Ss, c):
    return all((c - d, c) in Ss and (c, c + d) in Ss for d in (1, 2, 3))


def window_good(S, n, i):
    Ss = set(S)
    out = [((i + 3 + k - 1) % n) + 1 for k in range(1, n - 3)]
    for p, q, r in itertools.combinations(out, 3):
        st = {
            tuple(sorted(e))
            for e in [
                (i + 1, p),
                (i + 2, q),
                (i + 3, r),
                (p, i),
                (q, i + 1),
                (r, i + 2),
            ]
        }
        st = [e for e in st if e in Ss or e[1] - e[0] >= 4]
        if not has_nnk(sorted(set(st) | Ss), 4):
            return False
    return True


fams = []
for m in range(8, 14):
    found = enumerate_span(m)
    close = [
        S
        for S in found
        if (lambda c: len(c) == 3 and c[1] - c[0] <= 3 and c[2] - c[1] <= 3)(centres(S))
    ]
    print(
        f"span {m}: {len(found)} uncovered families, {len(close)} with both centre gaps <= 3",
        flush=True,
    )
    fams += [(m, S) for S in close]
assert len(fams) == 16, len(fams)

placements = 0
for m, S0 in fams:
    for A in range(MAXM + 1):
        for B in range(MAXM + 1):
            n = m + A + B
            S = [(a + A, b + A) for a, b in S0]
            c = centres(S)
            if not full_star(set(S), c[0]):
                S = sorted((n + 1 - b, n + 1 - a) for a, b in S)
                c = centres(S)
            assert full_star(set(S), c[0]), "no end centre with a full short star"
            assert window_good(S, n, c[0] - 1), (S0, A, B)
            placements += 1
print(
    f"16 families x margins 0..{MAXM}: {placements} placements, window [c-1, c+2] good in each"
)
print("ALL CHECKS PASSED")
