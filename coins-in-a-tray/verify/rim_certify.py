"""Rim-only rigid arrangements of coins 1/2, ..., 1/n in a unit tray, with exact relation tests.

A rim-only arrangement is a cyclic sequence of radii 1/j_1, ..., 1/j_m (every j in 2..n used) with angularly adjacent
coins tangent, sum of alpha_d = 2 pi over adjacent pairs (d = (j-1)(k-1), sin(alpha_d / 2) = 1/sqrt d), and no two
coins overlapping (user596229's reduction on MO 513668).
Stage 1: for each class a (squarefree part of d - 1), enumerate multiplicity vectors y with sum y_d alpha_d <= 2 pi
         and keep those that are exact relations (exact.py: prime-ideal valuations in Q(sqrt(-a)), Conway-Radin-Sadun
         splitting); the value is then an exact multiple of 2 pi / w and is read off by rounding.
Stage 2: combine classes so that the total is exactly 2 pi (rational arithmetic).
Stage 3: realise each multiset of d's as pair types (j, k), require every type, even degrees, then search Euler circuits
         for an order with no overlapping coins. Every overlap verdict records its margin; verdicts within 1e-6 of
         tangency are counted as ambiguous (there must be none).
Usage: rim_certify.py n [n ...]      MUTANT=1: drop the valuation test (rationality by rounding at 1e-3)."""
from __future__ import annotations

import itertools
import math
import os
import sys
from collections import Counter, defaultdict
from fractions import Fraction

from exact import is_relation, rim_data, roots_of_unity

MUTANT = os.environ.get("MUTANT") == "1"
STATS = {"trunc": 0, "ambiguous": 0, "min_margin": math.inf}


def alpha(d: int) -> float:
    return 2 * math.asin(1 / math.sqrt(d))


def prune(n: int):
    """Exact pruning with nonnegative multiplicities: in each class, if at some split prime every remaining d with a
    nonzero entry has the same sign, those d must have multiplicity 0. Iterate. Returns pairs, class lists, data,
    and the radii left with no usable neighbour pair."""
    pairs = defaultdict(list)
    for j in range(2, n + 1):
        for k in range(j, n + 1):
            pairs[(j - 1) * (k - 1)].append((j, k))
    cls = defaultdict(list)
    data = {}
    for d in pairs:
        a, v = rim_data(d)
        data[d] = v
        cls[a].append(d)
    if not MUTANT:
        for a in cls:
            alive = set(cls[a])
            changed = True
            while changed:
                changed = False
                primes = {q for d in alive for q in data[d]}
                for q in primes:
                    signs = {data[d][q] > 0 for d in alive if q in data[d]}
                    if len(signs) == 1:
                        alive -= {d for d in alive if q in data[d]}
                        changed = True
                        break
            cls[a] = sorted(alive)
    usable = {d for a in cls for d in cls[a]}
    stranded = [j for j in range(2, n + 1)
                if not any(d in usable for d in pairs if any(j in pr for pr in pairs[d]))]
    return pairs, cls, data, stranded


def stage1(n: int):
    pairs, cls, data, stranded = prune(n)
    out = {}
    for a, ds in cls.items():
        ds = sorted(ds)
        als = [alpha(d) for d in ds]
        vecs = [data[d] for d in ds]
        step = 2 * math.pi / (2 if a == 0 else roots_of_unity(a))  # alpha_1 = pi: unit pi
        opts = []

        def rec(i, acc, vec):
            if acc > 2 * math.pi + 1e-9:
                return
            if i == len(ds):
                if any(vec):
                    k = round(acc / step)
                    if MUTANT:
                        ok = abs(acc / step - k) < 1e-3
                    else:
                        ok = is_relation(vecs, vec)
                        if ok:
                            assert abs(acc / step - k) < 1e-9, "valuation test and numerics disagree"
                    if ok:
                        opts.append((tuple(vec), Fraction(k) * Fraction(2, 1) / (2 if a == 0 else roots_of_unity(a))))
                return
            m = 0
            while acc + m * als[i] <= 2 * math.pi + 1e-9:
                vec.append(m)
                rec(i + 1, acc + m * als[i], vec)
                vec.pop()
                m += 1

        rec(0, 0.0, [])
        if opts:
            out[a] = (ds, opts)
    return pairs, out


def stage2(out):
    classes = list(out.items())
    res = []

    def rec(i, tot, chosen):
        if tot > 2:
            return
        if i == len(classes):
            if tot == 2:
                res.append(list(chosen))
            return
        a, (ds, opts) = classes[i]
        rec(i + 1, tot, chosen)
        for vec, r in opts:
            chosen.append((ds, vec))
            rec(i + 1, tot + r, chosen)
            chosen.pop()

    rec(0, Fraction(0), [])
    return res


def cycles_from(n, pairs, combo, limit=2_000_000):
    dcount = Counter()
    for ds, vec in combo:
        for d, m in zip(ds, vec):
            dcount[d] += m
    ds = sorted(dcount)
    choices = [list(itertools.combinations_with_replacement(pairs[d], dcount[d])) for d in ds]
    for tried, pick in enumerate(itertools.product(*choices)):
        if tried > limit:
            STATS["trunc"] += 1
            return
        edges = [e for grp in pick for e in grp]
        deg = Counter()
        for j, k in edges:
            deg[j] += 1
            deg[k] += 1
        if set(deg) != set(range(2, n + 1)) or any(v % 2 for v in deg.values()):
            continue
        yield from euler_orders(n, edges)


def euler_orders(n, edges, cap=500_000):
    adj = Counter((min(j, k), max(j, k)) for j, k in edges)
    m = len(edges)
    start = min(min(e) for e in edges)
    seq, pos, found = [start], [0.0], [0]

    def overlaps(k, th):
        rk = 1 / k
        x, y = (1 - rk) * math.cos(th), (1 - rk) * math.sin(th)
        for t, p in zip(seq[:-1], pos[:-1]):
            rt = 1 / t
            u, v = (1 - rt) * math.cos(p), (1 - rt) * math.sin(p)
            gap = math.hypot(x - u, y - v) - (rk + rt)
            if abs(gap) < 1e-6:
                STATS["ambiguous"] += 1
            if gap < -1e-6:
                STATS["min_margin"] = min(STATS["min_margin"], -gap)
                return True
        return False

    def rec():
        if found[0] > cap:
            STATS["trunc"] += 1
            return
        if len(seq) == m + 1:
            if seq[-1] == seq[0]:
                found[0] += 1
                yield list(seq[:-1])
            return
        j = seq[-1]
        for k in range(2, n + 1):
            e = (min(j, k), max(j, k))
            if adj[e] == 0:
                continue
            th = pos[-1] + alpha((j - 1) * (k - 1))
            if len(seq) < m and overlaps(k, th):
                continue
            adj[e] -= 1
            seq.append(k)
            pos.append(th)
            yield from rec()
            adj[e] += 1
            seq.pop()
            pos.pop()

    yield from rec()


def canonical(s):
    k = len(s)
    return min([tuple(s[i:] + s[:i]) for i in range(k)] + [tuple(s[::-1][i:] + s[::-1][:i]) for i in range(k)])


def run(n: int) -> tuple[int, int, set]:
    stranded = prune(n)[3]
    if stranded:
        print(f"n={n}: radii with no usable rim neighbour: {['1/%d' % j for j in stranded]}", flush=True)
        return 0, 0, set()
    pairs, out = stage1(n)
    combos = stage2(out)
    sols = set()
    for combo in combos:
        for s in cycles_from(n, pairs, combo):
            sols.add(canonical(s))
    return len(out), len(combos), sols


if __name__ == "__main__":
    for n in map(int, sys.argv[1:]):
        ncls, ncombo, sols = run(n)
        print(f"n={n}: classes with relations {ncls}, exact 2pi multisets {ncombo}, rim cycles {len(sols)}"
              f" {sorted(sols, key=len)[:3]} | truncations {STATS['trunc']}, ambiguous {STATS['ambiguous']},"
              f" min overlap margin {STATS['min_margin']:.3g}", flush=True)
