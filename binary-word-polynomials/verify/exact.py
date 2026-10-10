"""Exact check of the fingerprint classes in out/c{n}.txt with integer polynomials, and basic stats."""
import sys
from pathlib import Path

OUT = Path(__file__).resolve().parent / "out"
from functools import lru_cache

def charpoly(w: str) -> tuple:
    a, b = (1,), (0,)            # P_0 = 1, P_{-1} = 0 ; coefficients low degree first
    for ch in w:
        x = int(ch)
        c = [0] * (len(a) + 1)
        for i, v in enumerate(a):
            c[i + 1] += v; c[i] -= x * v
        for i, v in enumerate(b):
            c[i] -= v
        a, b = tuple(c), a
    return a

def classes(n):
    out = []
    for line in open(OUT / f"c{n}.txt"):
        ws = line.split()[1:]
        polys = {}
        for w in ws:
            polys.setdefault(charpoly(w), []).append(w)
        out += [g for g in polys.values() if len(g) > 1]
    return out

if __name__ == "__main__":
    for n in range(1, int(sys.argv[1]) + 1):
        cl = classes(n)
        r = (2 ** n + 2 ** ((n + 1) // 2)) // 2
        extra = sum(len(g) - 1 for g in cl)
        sizes = {}
        for g in cl: sizes[len(g)] = sizes.get(len(g), 0) + 1
        print(n, "deficit", extra, "classes", len(cl), "sizes", dict(sorted(sizes.items())), "check r-a:", r)
