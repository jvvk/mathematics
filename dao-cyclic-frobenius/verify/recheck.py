"""Independent recheck (shares no code with verify_note.py): Frobenius numbers by Dijkstra on residues
modulo the smallest generator (round-robin Apery set), compared with (n-1)(P-1). Run: python3 -I recheck.py"""
import heapq
import itertools
from functools import reduce
from math import gcd


def gens_from(a):
    n = len(a)
    res = []
    for i in range(n):
        term, acc = 1, 1
        for k in range(i, i + n - 1):
            term = term * a[k % n]
            acc = acc + term
        res.append(acc)
    return res


def frobenius(g):
    m = min(g)
    dist = [None] * m
    dist[0] = 0
    heap = [(0, 0)]
    while heap:
        d, r = heapq.heappop(heap)
        if d > dist[r]:
            continue
        for x in g:
            nd, nr = d + x, (r + x) % m
            if dist[nr] is None or nd < dist[nr]:
                dist[nr] = nd
                heapq.heappush(heap, (nd, nr))
    return max(dist) - m


count = 0
bad = 0
for n, top in ((2, 8), (3, 8), (4, 5), (5, 4), (6, 3)):
    for a in itertools.product(range(1, top + 1), repeat=n):
        g = gens_from(a)
        if reduce(gcd, g) != 1:
            continue
        count += 1
        prod = reduce(lambda u, v: u * v, a, 1)
        if frobenius(g) != (n - 1) * (prod - 1):
            bad += 1
            print("MISMATCH", a, g)
print(f"recheck: {count} coprime lists, {bad} mismatches")
print("ALL PASS" if bad == 0 else "FAILED")
