"""Second, independent decision of chess realizability, in cvc5 rather than Z3.

Shares no code with src/realize.py and uses a different model: piece types are solver variables
(no enumeration of type assignments and no pruning rule), and slider attacks are written ray by ray.
For each of the eight directions d, b lies on the ray from a at step L >= 1, and a piece blocks when
it sits on the same ray at a step strictly between 0 and L. Coordinates are unbounded integers.

Usage: .venv/bin/python verify/second.py            (the 23 classes on 6 points, in class order)
"""

from __future__ import annotations

import sys
import time
from pathlib import Path

from cvc5.pythonic import And, If, Int, Not, Or, Solver, sat, unsat

sys.path.insert(0, str(Path(__file__).resolve().parent.parent / "src"))
from digraphs import all_classes

sys.path.insert(0, str(Path(__file__).resolve().parent))
from check import capture_graph

K, Q, R, B, N = range(5)
NAMES = "KQRBN"
ORTH = [(1, 0), (-1, 0), (0, 1), (0, -1)]
DIAG = [(1, 1), (1, -1), (-1, 1), (-1, -1)]


def on_ray(p, q, d, lo_excl, hi):
    """q = p + j*d for some integer j with lo_excl < j and (j < hi, or j == hi when hi is an int)."""
    (px, py), (qx, qy) = p, q
    sx, sy = d
    j = (qx - px) * sx if sx else (qy - py) * sy
    same = And(qx == px + sx * j, qy == py + sy * j)
    return j, And(same, j > lo_excl)


def ray_attack(pos, a, b, d):
    j, hit = on_ray(pos[a], pos[b], d, 0, None)
    blockers = []
    for c in range(len(pos)):
        if c not in (a, b):
            jc, on = on_ray(pos[a], pos[c], d, 0, None)
            blockers.append(And(on, jc < j))
    if not blockers:
        return hit
    return And(hit, Not(blockers[0] if len(blockers) == 1 else Or(blockers)))


def attack(pos, t, a, b):
    dx = pos[b][0] - pos[a][0]
    dy = pos[b][1] - pos[a][1]
    king = And(dx >= -1, dx <= 1, dy >= -1, dy <= 1)
    knight = Or(
        [
            And(dx == u, dy == v)
            for u in (-2, -1, 1, 2)
            for v in (-2, -1, 1, 2)
            if abs(u) != abs(v)
        ]
    )
    rook = Or([ray_attack(pos, a, b, d) for d in ORTH])
    bishop = Or([ray_attack(pos, a, b, d) for d in DIAG])
    return If(
        t[a] == K,
        king,
        If(
            t[a] == N,
            knight,
            If(t[a] == R, rook, If(t[a] == B, bishop, Or(rook, bishop))),
        ),
    )


def decide(arcs, n: int):
    arcs = set(arcs)
    pos = [(Int(f"x{i}"), Int(f"y{i}")) for i in range(n)]
    t = [Int(f"t{i}") for i in range(n)]
    s = Solver()
    s.add(pos[0][0] == 0, pos[0][1] == 0)
    for i in range(n):
        s.add(t[i] >= 0, t[i] <= 4)
        for j in range(i + 1, n):
            s.add(Or(pos[i][0] != pos[j][0], pos[i][1] != pos[j][1]))
    for a in range(n):
        for b in range(n):
            if a != b:
                e = attack(pos, t, a, b)
                s.add(e if (a, b) in arcs else Not(e))
    r = s.check()
    if r == sat:
        m = s.model()
        types = "".join(NAMES[m[v].as_long()] for v in t)
        p = [(m[x].as_long(), m[y].as_long()) for x, y in pos]
        ok = capture_graph(types, p) == arcs
        return f"REALIZABLE ({'checked' if ok else 'CHECK FAILED'}) {types} {p}"
    return "NONE" if r == unsat else "UNKNOWN"


def main() -> None:
    classes = all_classes(6)
    for i in map(int, sys.argv[1:] or range(len(classes))):
        t0 = time.time()
        v = decide(sorted(classes[i]), 6)
        print(f"class{i}: {v} {time.time() - t0:.1f}s", flush=True)


if __name__ == "__main__":
    main()
