"""Independent check of stage-2 certificates (two tiles per period).

A line "id proper|reflection group=AxB phi=(..)(..) g=permXY..,sign+-.." claims
that P and g(P) + t tile Z^m periodically under L = ker(phi), for some t.
This script re-derives everything from scratch (own group arithmetic, own
action of g, no masks or canonical forms):
  1. phi is onto G (the images of e_1..e_m generate G), so [Z^m : L] = |G|;
  2. there is s in G with phi(g(P)) + s equal to G minus phi(P), and both
     phi(P) and phi(g(P)) have |P| distinct values;
  3. a vector t with phi(t) = s is found by search, and then every residue
     class of Z^m / L is covered exactly once by P and g(P) + t.
Step 3 restates 1-2 as a covering statement: with R a set of |G| points, one
in each class, each x in R lies in exactly one tile of {P + L, g(P) + t + L}.

g acts by g(e_j) = sign_j * e_{perm_j}, as in stage2.c.
"""

from __future__ import annotations

import itertools
import re
import sys


def parse_cells(path: str) -> dict[int, list[tuple[int, ...]]]:
    out = {}
    for line in open(path):
        i = int(line.split()[0])
        out[i] = [
            tuple(map(int, c.split(",")))
            for c in re.findall(r"\(([-\d,]+)\)", line.split("lattice=")[0])
        ]
    return out


class Group:
    def __init__(self, factors: list[int]) -> None:
        self.f = factors

    def add(self, x: tuple[int, ...], y: tuple[int, ...]) -> tuple[int, ...]:
        return tuple((a + b) % n for a, b, n in zip(x, y, self.f))

    def scale(self, x: tuple[int, ...], k: int) -> tuple[int, ...]:
        return tuple((a * k) % n for a, n in zip(x, self.f))

    def zero(self) -> tuple[int, ...]:
        return tuple(0 for _ in self.f)

    def order(self) -> int:
        o = 1
        for n in self.f:
            o *= n
        return o

    def elements(self) -> set[tuple[int, ...]]:
        return set(itertools.product(*(range(n) for n in self.f)))


def check(line: str, cells: dict[int, list[tuple[int, ...]]]) -> bool:
    tok = line.split()
    uid, kind = int(tok[0]), tok[1]
    if kind == "none":
        return True
    G = Group([int(x) for x in re.search(r"group=([\dx]+)", line).group(1).split("x")])
    imgs = [
        tuple(map(int, c.split(",")))
        for c in re.findall(r"\(([\d,]+)\)", re.search(r"phi=(\S+)", line).group(1))
    ]
    gm = re.search(r"g=perm(\d+),sign([+-]+)", line)
    perm = [int(c) for c in gm.group(1)]
    sign = [1 if c == "+" else -1 for c in gm.group(2)]
    # det g = sign of the permutation times the product of the signs; it must match the label
    inversions = sum(1 for i in range(len(perm)) for j in range(i + 1, len(perm)) if perm[i] > perm[j])
    det = (-1) ** inversions
    for sg in sign:
        det *= sg
    if det != (1 if kind == "proper" else -1):
        return False
    P = cells[uid]
    m = len(P[0])

    def phi(v: tuple[int, ...]) -> tuple[int, ...]:
        r = G.zero()
        for vj, a in zip(v, imgs):
            r = G.add(r, G.scale(a, vj))
        return r

    def act(v: tuple[int, ...]) -> tuple[int, ...]:
        w = [0] * m
        for j in range(m):
            w[perm[j]] += sign[j] * v[j]
        return tuple(w)

    # 1. onto
    span = {G.zero()}
    while True:
        new = {G.add(x, a) for x in span for a in imgs} | span
        if new == span:
            break
        span = new
    if len(span) != G.order():
        return False
    # 2. complementary images
    A = [phi(p) for p in P]
    gP = [act(p) for p in P]
    B = [phi(q) for q in gP]
    if len(set(A)) != len(P) or len(set(B)) != len(P):
        return False
    comp = G.elements() - set(A)
    shifts = [s for s in G.elements() if {G.add(b, s) for b in B} == comp]
    if not shifts:
        return False
    # 3. explicit t and covering of one point per residue class
    s = shifts[0]
    # one vector over each element of G, by breadth-first search along +-e_j (phi is onto)
    reps: dict[tuple[int, ...], tuple[int, ...]] = {G.zero(): (0,) * m}
    frontier = [(0,) * m]
    while frontier and len(reps) < G.order():
        nxt = []
        for v in frontier:
            for j in range(m):
                for sgn in (1, -1):
                    w = tuple(v[i] + (sgn if i == j else 0) for i in range(m))
                    g = phi(w)
                    if g not in reps:
                        reps[g] = w
                        nxt.append(w)
        frontier = nxt
    t = reps[s]
    tiles = [P, [tuple(q[j] + t[j] for j in range(m)) for q in gP]]
    for x in reps.values():
        hits = sum(
            1
            for tile in tiles
            for c in tile
            if phi(tuple(xi - ci for xi, ci in zip(x, c))) == G.zero()
        )
        if hits != 1:
            return False
    return True


def main(cert: str, s2: str) -> None:
    cells = parse_cells(cert)
    lines = [ln for ln in open(s2) if ln.strip()]
    ok = sum(check(ln, cells) for ln in lines)
    kinds = {
        k: sum(1 for ln in lines if ln.split()[1] == k)
        for k in ("proper", "reflection", "none")
    }
    print(f"{s2}: lines={len(lines)} verified={ok} {kinds}")


if __name__ == "__main__":
    main(sys.argv[1], sys.argv[2])
