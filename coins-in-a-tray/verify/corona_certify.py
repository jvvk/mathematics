"""Closed coronas with exact relation tests (MO 513668); replaces the 80-digit test of corona.py.

Around a coin of curvature m, a closed corona is a cyclic list of neighbours (coins 1/2..1/n, or the tray T at most
once), each tangent to the centre coin and to the next neighbour, no two overlapping, contact directions turning by
exactly 2 pi. The angle between contacts with neighbours a, b has rational cosine p/q (corona.cos_angle). With
q^2 - p^2 = s^2 a (a squarefree), theta = arg(p + s sqrt(-a)); relations within a class are decided exactly by
prime-ideal valuations (exact.py), and their value is then a multiple of pi / w. Angles with cosine 0, +-1/2, +-1 are
exact rational multiples of pi.
Overlap and containment verdicts record their margins; verdicts within 1e-6 of the boundary are counted as
ambiguous. Usage: corona_certify.py n   (prints the coronas of every coin and the reach obstruction).
MUTANT=1 replaces the exact relation test by rounding at tolerance 2e-2."""
from __future__ import annotations

import itertools
import math
import sys
from collections import Counter, defaultdict
from fractions import Fraction

import corona as C
import os

from exact import roots_of_unity, squarefree_split, valuation_vector, is_relation

MUTANT = os.environ.get("MUTANT") == "1"  # relation test by rounding at tolerance 2e-2

T = C.T
STATS = {"trunc": 0, "ambiguous": 0, "min_margin": math.inf}
RATIONAL = {Fraction(1): Fraction(0), Fraction(1, 2): Fraction(1, 3), Fraction(0): Fraction(1, 2),
            Fraction(-1, 2): Fraction(2, 3), Fraction(-1): Fraction(1)}  # cos -> angle / pi


def angle_data(c: Fraction):
    """(class, valuation vector, angle/pi if rational else None)."""
    if c in RATIONAL:
        return 0, {}, RATIONAL[c]
    p, q = c.numerator, c.denominator
    a, s = squarefree_split(q * q - p * p)
    return a, valuation_vector(a, p, s), None


def coronas(m: int, n: int, cap: int = 300_000):
    at = C.angle_types(m, n)
    groups = defaultdict(list)
    info = {}
    for pr, c in at.items():
        a, v, r = angle_data(c)
        info[pr] = (v, r)
        groups[a].append(pr)
    opts = {}
    for a, prs in groups.items():
        ths = [math.acos(float(at[pr])) for pr in prs]
        vecs = [info[pr][0] for pr in prs]
        res = []

        def rec(i, acc, vec):
            if acc > 2 * math.pi + 1e-9:
                return
            if i == len(prs):
                if any(vec):
                    if a == 0:
                        val = sum(k * info[pr][1] for pr, k in zip(prs, vec))
                        res.append((tuple(vec), val))
                    else:
                        step = math.pi / roots_of_unity(a)
                        k = round(acc / step)
                        if MUTANT:
                            ok = abs(acc / step - k) < 2e-2
                        else:
                            ok = is_relation(vecs, vec)
                            assert not ok or abs(acc / step - k) < 1e-9
                        if ok:
                            res.append((tuple(vec), Fraction(k, roots_of_unity(a))))
                return
            k = 0
            while acc + k * ths[i] <= 2 * math.pi + 1e-9:
                vec.append(k)
                rec(i + 1, acc + k * ths[i], vec)
                vec.pop()
                k += 1
                if ths[i] == 0:
                    break

        rec(0, 0.0, [])
        if res:
            opts[a] = (prs, res)
    keys = list(opts)
    combos = []

    def rec2(i, tot, chosen):
        if tot > 2:
            return
        if i == len(keys):
            if tot == 2:
                combos.append(list(chosen))
            return
        rec2(i + 1, tot, chosen)
        prs, res = opts[keys[i]]
        for vec, r in res:
            chosen.append((prs, vec))
            rec2(i + 1, tot + r, chosen)
            chosen.pop()

    rec2(0, Fraction(0), [])
    sols = set()
    for combo in combos:
        edges = []
        for prs, vec in combo:
            for pr, k in zip(prs, vec):
                edges += [pr] * k
        deg = Counter()
        for a_, b_ in edges:
            deg[a_] += 1
            deg[b_] += 1
        if any(v % 2 for v in deg.values()) or deg[T] > 2:
            continue
        for s in circuits(m, edges, at, cap):
            k = len(s)
            reps = [tuple(s[i:] + s[:i]) for i in range(k)] + [tuple(s[::-1][i:] + s[::-1][:i]) for i in range(k)]
            sols.add(min(reps))
    return sols, len(combos)


def circuits(m, edges, at, cap):
    adj = Counter((min(a, b), max(a, b)) for a, b in edges)
    E = len(edges)
    start = T if any(T in e for e in adj) else min(x for e in adj for x in e)
    seq, ang = [start], [0.0]
    rm = 1 / m

    def centre(x, th):
        if x == T:
            return (-(1 - rm) * math.cos(th), -(1 - rm) * math.sin(th))
        d = rm + 1 / x
        return (d * math.cos(th), d * math.sin(th))

    def note(gap):
        if abs(gap) < 1e-6:
            STATS["ambiguous"] += 1

    def ok(x, th):
        cx = centre(x, th)
        for y, t in zip(seq[:-1], ang[:-1]):
            if len(seq) == E and y == seq[0]:
                continue
            cy = centre(y, t)
            dist = math.hypot(cx[0] - cy[0], cx[1] - cy[1])
            if x == T or y == T:
                r = 1 / (y if x == T else x)
                gap = (1 - r) - dist
            else:
                gap = dist - (1 / x + 1 / y)
            note(gap)
            if gap < -1e-6:
                STATS["min_margin"] = min(STATS["min_margin"], -gap)
                return False
        return True

    def fits(sq, an):
        if T in sq:
            return True
        disks = [((0.0, 0.0), rm)] + [(centre(x, t), 1 / x) for x, t in zip(sq, an)]
        for (p, r1), (q, r2) in itertools.combinations(disks, 2):
            gap = 2 - (math.hypot(p[0] - q[0], p[1] - q[1]) + r1 + r2)
            note(gap)
            if gap < -1e-6:
                STATS["min_margin"] = min(STATS["min_margin"], -gap)
                return False
        return True

    count = [0]

    def rec():
        if count[0] > cap:
            STATS["trunc"] += 1
            return
        if len(seq) == E + 1:
            if seq[-1] == seq[0] and fits(seq[:-1], ang[:-1]):
                count[0] += 1
                yield list(seq[:-1])
            return
        a = seq[-1]
        for e in list(adj):
            if adj[e] == 0 or a not in e:
                continue
            b = e[1] if e[0] == a else e[0]
            if b == T and T in seq[1:]:
                continue
            th = ang[-1] + math.acos(float(at[e]))
            if len(seq) < E and not ok(b, th):
                continue
            adj[e] -= 1
            seq.append(b)
            ang.append(th)
            yield from rec()
            adj[e] += 1
            seq.pop()
            ang.pop()

    yield from rec()


def reach(n: int, verbose: bool = True):
    cor = {}
    for m in range(2, n + 1):
        cor[m], _ = coronas(m, n)
        if verbose:
            lab = [tuple("T" if x == T else x for x in s) for s in sorted(cor[m], key=len)[:4]]
            print(f"  1/{m}: {len(cor[m])} closed coronas {lab}", flush=True)
    R = {m for m, ss in cor.items() if any(T in s for s in ss)}
    changed = True
    while changed:
        changed = False
        for m, ss in cor.items():
            if m not in R and any(any(x in R for x in s) for s in ss):
                R.add(m)
                changed = True
    return sorted(R), [m for m in range(2, n + 1) if m not in R]


if __name__ == "__main__":
    for n in map(int, sys.argv[1:]):
        R, miss = reach(n)
        print(f"n={n}: cannot be linked to the tray {['1/%d' % m for m in miss]} | truncations {STATS['trunc']},"
              f" ambiguous {STATS['ambiguous']}, min margin {STATS['min_margin']:.3g}", flush=True)
