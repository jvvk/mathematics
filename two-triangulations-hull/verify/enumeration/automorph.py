"""Combinatorial automorphisms of witness order types.

A bijection pi is orientation-preserving (sign +1) if orient(pi i, pi j, pi k) = orient(i, j, k) for all
triples, orientation-reversing (sign -1) if it negates every triple. A set is achiral iff some -1 map exists.
Hull vertices must map to hull vertices in cyclic order, so only 2h * (n-h)! candidates are tried.
usage: python3 automorph.py witnessesNN.txt
"""
from __future__ import annotations

import itertools
import re
import sys

Pt = tuple[int, int]


def orient(p: Pt, q: Pt, r: Pt) -> int:
    v = (q[0] - p[0]) * (r[1] - p[1]) - (q[1] - p[1]) * (r[0] - p[0])
    return (v > 0) - (v < 0)


def hull_ccw(P: list[Pt]) -> list[int]:
    idx = sorted(range(len(P)), key=lambda i: P[i])
    def chain(seq):
        out: list[int] = []
        for i in seq:
            while len(out) >= 2 and orient(P[out[-2]], P[out[-1]], P[i]) <= 0:
                out.pop()
            out.append(i)
        return out
    lo, up = chain(idx), chain(idx[::-1])
    return lo[:-1] + up[:-1]


def automorphisms(P: list[Pt]) -> list[tuple[int, tuple[int, ...]]]:
    n = len(P)
    O = {t: orient(P[t[0]], P[t[1]], P[t[2]]) for t in itertools.permutations(range(n), 3)}
    H = hull_ccw(P)
    h = len(H)
    inner = [i for i in range(n) if i not in H]
    found = []
    for shift in range(h):
        for d in (1, -1):
            img = {H[k]: H[(shift + d * k) % h] for k in range(h)}
            sign = d
            for perm in itertools.permutations(inner):
                pi = dict(img)
                pi.update(zip(inner, perm))
                if all(O[(pi[a], pi[b], pi[c])] == sign * O[(a, b, c)]
                       for a, b, c in itertools.combinations(range(n), 3)):
                    found.append((sign, tuple(pi[i] for i in range(n))))
    return found


def main() -> None:
    for line in open(sys.argv[1]):
        P = [(int(x), int(y)) for x, y in re.findall(r"\((\d+),(\d+)\)", line)]
        auts = automorphisms(P)
        rot = sum(1 for s, _ in auts if s == 1)
        ref = sum(1 for s, _ in auts if s == -1)
        if rot > 1 or ref > 0 or len(P) == 9:
            print(line.split(":")[0].strip(), f"orientation-preserving={rot} reversing={ref}")


if __name__ == "__main__":
    main()
