"""Theorem 3, Lemma 9 (Table 1) and the exceptional arrangement of Lemma 12: every certificate checked explicitly.

For each part (a)-(f) of Lemma 9, every n in range, every centre c, every admissible pair A, B of short edges and every
position p < q < r of the star on the window (cyclic order after the window), the four edges named by Table 1 are
present (in S, or a star chord (4) of length >= 4), have eight distinct ends and no nested pair. The row is chosen by
the table's case conditions, so the check also confirms that the rows are exhaustive. No search is used.
The exceptional arrangement: centres a, a+4, a+8, star on (a+2, a+5) with p = a-2, q < r in {a-1, a, a+1}: the chords
(a-2,a+3), (q,a+4), (r,a+5) are long, differ from the missing edge (a-2,a+2), and with (a+8,a+9) form an NN4.

Usage: python3 k4_windows.py [--quick]    (full: n <= 19, about a minute; quick: n <= 13)
"""

import itertools
import sys

if not __debug__:
    sys.exit("refusing to run under python -O: the checks are assertions")

NMAX = 13 if "--quick" in sys.argv else 19


def nested(e, f):
    return (e[0] < f[0] and f[1] < e[1]) or (f[0] < e[0] and e[1] < f[1])


def is_nn4(M, present):
    M = [tuple(sorted(e)) for e in M]
    return (
        all(present(e) for e in M)
        and len({v for e in M for v in e}) == 8
        and not any(nested(x, y) for x, y in itertools.combinations(M, 2))
    )


def star_positions(n, i):
    """p < q < r in cyclic order after i+3 (vertices right of the window first, then those left of it)."""
    out = [((i + 3 + k - 1) % n) + 1 for k in range(1, n - 3)]
    return itertools.combinations(out, 3)


def short_edges(lo, hi):
    return [(u, v) for u in range(max(lo, 1), hi + 1) for v in range(u + 1, min(hi, u + 3) + 1)]


def pairs(edges):
    for A, B in itertools.combinations(edges, 2):
        if not set(A) & set(B) and not nested(A, B):
            yield A, B


def chords(i, p, q, r):
    """The six chords (4) of the star on the window [i, i+3], normalised (min, max)."""
    return {tuple(sorted(e)) for e in [(i + 1, p), (i + 2, q), (i + 3, r), (p, i), (q, i + 1), (r, i + 2)]}


def run_part(name, i_off, need, ab, row):
    """need(c): short edges assumed in S; ab(n, c): list of (A, B) (B may be None); row(c, p, q, r, A, B): matching.
    An edge of a row counts as present only if it is in S, or it is one of the six star chords (4) and has length
    at least 4."""
    count = 0
    for n in range(7, NMAX + 1):
        for c in range(1, n + 1):
            S0 = need(c)
            i = c + i_off
            if i < 1 or i + 3 > n or any(not (1 <= x < y <= n) for x, y in S0):
                continue
            for A, B in ab(n, c):
                S = set(S0) | {e for e in (A, B) if e is not None}
                for p, q, r in star_positions(n, i):
                    ch = chords(i, p, q, r)
                    present = lambda e, S=S, ch=ch: e in S or (e in ch and e[1] - e[0] >= 4)
                    M = row(c, p, q, r, A, B)
                    assert is_nn4(M, present), (name, n, c, A, B, p, q, r, M)
                    count += 1
    print(f"part {name}: {count} placements, every Table 1 certificate valid")
    return count


R = lambda v, c, w: v > w  # 'right of the window' means after its last vertex w

# (a) W = [c-2, c+1]; (c-3,c), (c,c+2) in S; A, B short, all ends >= c+3
run_part(
    "a",
    -2,
    lambda c: [(c - 3, c), (c, c + 2)],
    lambda n, c: list(pairs(short_edges(c + 3, n))),
    lambda c, p, q, r, A, B: (
        [(r, c + 1), (c, c + 2), A, B]
        if r <= c - 3
        else (
            [(c - 3, c), (c - 2, c + 2), A, B]
            if r == c + 4
            else [(c - 3, c), (c - 2, p), (c - 1, q), (c + 1, r)]
        )
    ),
)

# (b) W = [c-1, c+2]; (c-2,c), (c,c+3) in S; A, B short, all ends >= c+4
run_part(
    "b",
    -1,
    lambda c: [(c - 2, c), (c, c + 3)],
    lambda n, c: list(pairs(short_edges(c + 4, n))),
    lambda c, p, q, r, A, B: (
        [(r, c + 2), (c, c + 3), A, B]
        if r <= c - 2
        else (
            [(c - 2, c), (c - 1, c + 3), A, B]
            if p == c + 3
            else [(c - 2, c), (c - 1, p), (c + 1, q), (c + 2, r)]
        )
    ),
)


# (c) W = [c-1, c+2]; (c-3,c), (c,c+2) in S; A, B short, all ends >= c+4
def row_c(c, p, q, r, A, B):
    m = min(A[0], B[0])
    if c + 2 < p < m:
        return [(c - 1, p), (c - 3, c), A, B]
    if r <= c - 3:
        return [(r, c + 1), (c, c + 2), A, B]
    if r == c - 2 and q <= c - 3:
        return [(q, c), (c - 2, c + 2), A, B]
    if r == c - 2:
        return [(c - 1, p), (c + 1, q), (c - 2, c + 2), (c - 3, c)]
    return [(c - 1, p), (c + 1, q), (c + 2, r), (c - 3, c)]


run_part(
    "c",
    -1,
    lambda c: [(c - 3, c), (c, c + 2)],
    lambda n, c: list(pairs(short_edges(c + 4, n))),
    row_c,
)


# (d) W = [c-1, c+2]; (c-3,c), (c,c+3) in S; A short with ends <= c-4, B short with ends >= c+4
def row_d(c, p, q, r, A, B):
    if r > c + 2:
        return [A, (c - 1, p), (c, q), (c + 1, r)]
    if q < c - 1:
        return [(q, c + 1), (r, c + 2), (c, c + 3), B]
    if q >= c + 5:
        return [A, (c - 3, c), (c - 1, p), (c + 1, q)]
    return [A, (c - 3, c), (c - 1, c + 3), B]


run_part(
    "d",
    -1,
    lambda c: [(c - 3, c), (c, c + 3)],
    lambda n, c: [(A, B) for A in short_edges(1, c - 4) for B in short_edges(c + 4, n)],
    row_d,
)

# (e) W = [c-1, c+2]; (c-2,c), (c,c+3), (c+1,c+4) in S; B short with ends >= c+5
run_part(
    "e",
    -1,
    lambda c: [(c - 2, c), (c, c + 3), (c + 1, c + 4)],
    lambda n, c: [(None, B) for B in short_edges(c + 5, n)],
    lambda c, p, q, r, A, B: (
        [(r, c + 2), (c, c + 3), (c + 1, c + 4), B]
        if r <= c - 2
        else (
            [(c - 2, c), (c - 1, c + 3), (c + 1, c + 4), B]
            if p == c + 3
            else [(c - 2, c), (c - 1, p), (c + 1, q), (c + 2, r)]
        )
    ),
)

# (f) W = [c-2, c+1]; (c-3,c), (c,c+3), (c+2,c+4) in S; B short with ends >= c+6
run_part(
    "f",
    -2,
    lambda c: [(c - 3, c), (c, c + 3), (c + 2, c + 4)],
    lambda n, c: [(None, B) for B in short_edges(c + 6, n)],
    lambda c, p, q, r, A, B: (
        [(r, c + 1), (c, c + 3), (c + 2, c + 4), B]
        if r <= c - 3
        else (
            [(c - 3, c), (c - 1, c + 3), (c + 2, c + 4), B]
            if r == c + 4
            else [(c - 3, c), (c - 2, p), (c - 1, q), (c + 1, r)]
        )
    ),
)

# Exceptional arrangement (Lemma 12): a = centre, missing edge (a-2, a+2)
cnt = 0
for n in range(16, NMAX + 9):
    for a in range(4, n - 10):
        i = a + 2
        for q, r in itertools.combinations([a - 1, a, a + 1], 2):
            chords3 = [(a - 2, a + 3), (q, a + 4), (r, a + 5)]
            assert set(chords3) <= chords(i, a - 2, q, r)  # they are chords (4) of the star with p = a-2
            assert all(e[1] - e[0] >= 4 and e != (a - 2, a + 2) for e in chords3)
            S = set(chords3) | {(a + 8, a + 9)}
            assert is_nn4(chords3 + [(a + 8, a + 9)], lambda e: e in S)
            cnt += 1
print(f"exceptional arrangement: {cnt} placements, NN4 found in each")
print("ALL CHECKS PASSED")
