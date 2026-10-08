"""Independent recheck of the MO 442949 certificates (shares no code with codex-2026-10-08/).

Exact arithmetic throughout: a turn with tan(A/2) = t/d is the Gaussian rational (d^2 - t^2 + 2i d t)/(d^2 + t^2);
every direction of an arrangement is an integer vector over the common denominator prod(d^2 + t_j^2), so squared
spans compare as integers. For each witness the checker
  * verifies distinct positive sorted data and total turn < pi/2 (exact quadrant test of all prefix products),
  * finds the winning reversal class by enumeration: ALL classes for n <= 6 and for the two Table 2 examples;
    for larger n, the structural candidates (Theorem 2.1, proved), counting them against M_n = 2 C(2n-5, n-3) - 2,
  * checks the winner is unique, equals the stored pattern, and (main data) lies in the recursive family C_n,
  * checks the stored exact margin.
Run: python recheck.py [--fast]    (--fast skips the two 1.8-million-class n = 7 enumerations)
"""

from __future__ import annotations

import itertools
import json
import sys
from fractions import Fraction
from math import comb
from pathlib import Path

HERE = Path(__file__).resolve().parent
DATA = HERE.parent

Gauss = tuple[int, int]


def gmul(a: Gauss, b: Gauss) -> Gauss:
    return (a[0] * b[0] - a[1] * b[1], a[0] * b[1] + a[1] * b[0])


def turn_unit(t: int, d: int) -> tuple[Gauss, int]:
    """e^{iA} = num / den with tan(A/2) = t/d."""
    return (d * d - t * t, 2 * d * t), d * d + t * t


def directions(ts: list[int], d: int, q: tuple[int, ...]) -> tuple[list[Gauss], int]:
    """Integer direction vectors (over a common denominator) for turn order q."""
    units = [turn_unit(t, d) for t in ts]
    den = 1
    for _, s in units:
        den *= s
    cur: Gauss = (1, 0)
    curden = 1
    out = []
    for i in range(len(q) + 1):
        scale = den // curden
        out.append((cur[0] * scale, cur[1] * scale))
        if i < len(q):
            u, s = units[q[i]]
            cur = gmul(cur, u)
            curden *= s
    return out, den


def span2(lengths: list[int], p: tuple[int, ...], dirs: list[Gauss]) -> int:
    x = sum(lengths[p[i]] * dirs[i][0] for i in range(len(p)))
    y = sum(lengths[p[i]] * dirs[i][1] for i in range(len(p)))
    return x * x + y * y


def total_turn_below_half_pi(ts: list[int], d: int) -> bool:
    cur: Gauss = (1, 0)
    for t in ts:
        cur = gmul(cur, turn_unit(t, d)[0])
        if cur[1] <= 0:  # a prefix reached angle >= pi
            return False
    return cur[0] > 0 and cur[1] > 0


def all_classes(n: int):
    for p in itertools.permutations(range(n)):
        for q in itertools.permutations(range(n - 1)):
            if (p, q) <= (p[::-1], q[::-1]):
                yield p, q


def unimodal_p(n: int):
    """Length-rank lists 0, S increasing, n-1, complement decreasing, 1."""
    mid = range(2, n - 1)
    for r in range(len(mid) + 1):
        for S in itertools.combinations(mid, r):
            yield (0, *S, n - 1, *sorted(set(mid) - set(S), reverse=True), 1)


def valley_q(n: int):
    """Turn-rank lists decreasing to 0 then increasing."""
    rest = range(1, n - 1)
    for r in range(len(rest) + 1):
        for S in itertools.combinations(rest, r):
            yield (*sorted(S, reverse=True), 0, *sorted(set(rest) - set(S)))


def wide(n: int):
    """The 2^(2n-5) candidates of Section 3.1: unimodal p with 0 and 1 at the ends, any valley q."""
    for p in unimodal_p(n):
        for q in valley_q(n):
            yield p, q


def structural(n: int):
    """Candidates allowed by Theorem 2.1: also first turn descends, last ascends (n >= 4), and the longest
    segment is incident to the smallest turn."""
    for p, q in wide(n):
        if n >= 3 and not q[0] > q[1]:
            continue
        if n >= 4 and not q[-2] < q[-1]:
            continue
        if q.index(0) not in (p.index(n - 1) - 1, p.index(n - 1)):
            continue
        yield p, q


def normalize(p, q):
    return (p, q) if p[0] == 0 else (p[::-1], q[::-1])


def best(lengths, ts, d, pool):
    vals = {}
    cache = {}
    for p, q in pool:
        if q not in cache:
            cache[q] = directions(ts, d, q)
        dirs, den = cache[q]
        vals[(p, q)] = span2(lengths, p, dirs)
    ranked = sorted(vals.items(), key=lambda kv: -kv[1])
    (wp, wv), (_, rv) = ranked[0], ranked[1]
    den = cache[wp[1]][1]
    return normalize(*wp), Fraction(wv - rv, den * den), len(vals)


def family(n: int) -> set:
    if n == 1:
        return {((0,), ())}
    if n == 2:
        return {((0, 1), (0,))}
    if n == 3:
        return {((0, 2, 1), (1, 0))}
    out = set()
    for k in range(2, n):
        for P, Q in family(n - k + 1):
            out.add(
                (
                    (0, *[x + k - 1 for x in reversed(P)], *range(k - 2, 0, -1)),
                    (n - 2, *reversed(Q), *range(n - k, n - 2)),
                )
            )
    for P, Q in family(n - 2):
        out.add(((0, *[x + 2 for x in P], 1), (n - 3, *Q, n - 2)))
    return out


def check_witness(w: dict, pool_kind: str, in_family: bool = True) -> tuple:
    L, ts, d = w["lengths"], w["tangent_numerators"], w["tangent_denominator"]
    n = len(L)
    assert L[0] > 0 and all(a < b for a, b in zip(L, L[1:])), (
        "lengths not distinct positive sorted"
    )
    assert ts[0] > 0 and all(a < b for a, b in zip(ts, ts[1:])), (
        "turns not distinct positive sorted"
    )
    assert total_turn_below_half_pi(ts, d), "total turn not below pi/2"
    if pool_kind == "all":
        pool = list(all_classes(n))
    else:
        pool = list(structural(n))
        if n >= 4:
            assert len(pool) == 2 * comb(2 * n - 5, n - 3) - 2, (
                "candidate count differs from M_n"
            )
    pat, margin, size = best(L, ts, d, pool)
    assert margin > 0, "winner not unique"
    assert pat == (tuple(w["p"]), tuple(w["q"])), (
        f"winner {pat} differs from stored {w['p'], w['q']}"
    )
    if in_family:
        assert pat in family(n), f"winner {pat} not in the recursive family"
    if "squared_distance_margin" in w:
        if "arrangements_checked" in w:          # stored margin is over all classes
            ref = margin if pool_kind == "all" else None
        else:                                     # stored margin is over the structural candidates
            wpool = list(wide(n))
            assert len(wpool) == 2 ** (2 * n - 5)
            wpat, ref, _ = best(L, ts, d, wpool)
            assert wpat == pat
        if ref is not None:
            assert ref == Fraction(w["squared_distance_margin"]), "stored margin differs"
    if "unrestricted_squared_distance_margin" in w and pool_kind == "all":
        assert margin == Fraction(w["unrestricted_squared_distance_margin"]), "stored unrestricted margin differs"
    return pat, margin, size


def main() -> None:
    fast = "--fast" in sys.argv
    # family counts
    b = [len(family(n)) for n in range(3, 12)]
    assert b == [1, 3, 6, 14, 31, 70, 157, 353, 793], b
    for n in range(6, 12):
        assert len(family(n)) == 2 * len(family(n - 1)) + len(family(n - 2)) - len(
            family(n - 3)
        )
    print("family sizes b_3..b_11 =", b, "(A006356), recurrence checked")

    for n in range(4, 9):
        rows = json.loads((DATA / f"exact-witnesses-{n}.json").read_text())
        kind = "all" if n <= 6 else "structural"
        pats = {check_witness(w, kind)[0] for w in rows}
        assert len(pats) == len(rows) == len(family(n)), (n, len(pats))
        assert pats == family(n)
        print(
            f"n={n}: {len(rows)} witnesses, {kind} enumeration, distinct winners = the whole family C_{n}"
        )

    for w in json.loads((DATA / "short-n4-witnesses.json").read_text()):
        check_witness(w, "all")
    print(
        "Table 1 short n=4 witnesses: unique optima over all 72 classes, margins match"
    )

    for w in json.loads((DATA / "new-n7-witnesses.json").read_text()):
        pat, margin, size = check_witness(w, "structural" if fast else "all")
        print(
            f"Table 2 witness {pat}: unique optimum over {size} classes, margin > {float(margin):.4g}"
        )

    rows = json.loads((DATA / "constructed-witnesses.json").read_text())
    for w in rows:
        check_witness(w, "structural")
    print(
        f"constructed witnesses: {len(rows)} unique optima (structural candidates), all in the family"
    )

    core = json.loads((DATA / "research" / "non-inheriting-core.json").read_text())
    whole = core["whole_witness"]
    check_witness(whole, "all")
    bare = dict(
        lengths=core["core_lengths"],
        tangent_numerators=core["core_tangent_numerators"],
        tangent_denominator=core["denominator"],
        p=core["bare_core_optimum"]["p"],
        q=core["bare_core_optimum"]["q"],
    )
    check_witness(bare, "all")
    print(
        "deletion example: whole chain optimum",
        tuple(map(tuple, (whole["p"], whole["q"]))),
        "; bare core optimum",
        tuple(map(tuple, (bare["p"], bare["q"]))),
        "(not the type-A parent)",
    )

    # beyond a semicircle: lengths 1,2,3, tan(A/2) = 3 and 4 (total turn > pi)
    vals = []
    for p in itertools.permutations(range(3)):
        for q in itertools.permutations(range(2)):
            if (p, q) <= (p[::-1], q[::-1]):
                dirs, den = directions([3, 4], 1, q)
                vals.append((Fraction(span2([1, 2, 3], p, dirs), den * den), p, q))
    vals.sort(reverse=True)
    assert sorted(v for v, _, _ in vals) == [
        Fraction(x, 85) for x in (26, 68, 234, 290, 900, 914)
    ]
    top = normalize(vals[0][1], vals[0][2])
    print(
        "beyond a semicircle: squared spans",
        [str(v) for v, _, _ in sorted(vals)],
        "winner",
        top,
    )
    print("ALL PASS")


if __name__ == "__main__":
    main()
