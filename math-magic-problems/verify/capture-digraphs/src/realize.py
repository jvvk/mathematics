"""Decide whether a digraph is the capture graph of a chess position, on an unbounded board.

Pieces K, Q, R, B, N (no pawns), any number of each, colour ignored: there is an arc a -> b exactly
when piece a attacks the square of piece b (sliders are blocked by any piece strictly between).
For each assignment of piece types to vertices, Z3 decides linear integer arithmetic over unbounded
coordinates, so UNSAT for every assignment means no position on any board realizes the digraph.

Usage: realize.py            (all 23 classes on 6 vertices, plus the open cases q, r, s)
"""

from __future__ import annotations

import sys
import time
from itertools import product

from z3 import And, If, Int, Not, Or, Solver, sat, unsat

from digraphs import OPEN, all_classes, canon

sys.path.insert(0, str(__import__('pathlib').Path(__file__).resolve().parent.parent / 'verify'))
from check import capture_graph  # independent simulator

TYPES = "KQRBN"


def absz(e):
    return If(e >= 0, e, -e)


def between(p, q, c):
    """Piece c lies strictly between p and q on a common rank, file or diagonal."""
    (xa, ya), (xb, yb), (xc, yc) = p, q, c
    bx = Or(And(xa < xc, xc < xb), And(xb < xc, xc < xa))
    by = Or(And(ya < yc, yc < yb), And(yb < yc, yc < ya))
    return Or(
        And(ya == yb, yc == ya, bx),
        And(xa == xb, xc == xa, by),
        And(xb - xa == yb - ya, xc - xa == yc - ya, bx),
        And(xb - xa == ya - yb, xc - xa == ya - yc, bx),
    )


def attacks(t: str, a: int, b: int, pos):
    (xa, ya), (xb, yb) = pos[a], pos[b]
    dx, dy = absz(xb - xa), absz(yb - ya)
    if t == "K":
        return And(dx <= 1, dy <= 1)
    if t == "N":
        return Or(And(dx == 1, dy == 2), And(dx == 2, dy == 1))
    clear = Not(
        Or(
            [
                between(pos[a], pos[b], pos[c])
                for c in range(len(pos))
                if c not in (a, b)
            ]
        )
    )
    orth, diag = Or(dx == 0, dy == 0), dx == dy
    line = {"R": orth, "B": diag, "Q": Or(orth, diag)}[t]
    return And(line, clear)


def plausible(types: str, arcs: set[tuple[int, int]], n: int) -> bool:
    """Cheap necessary conditions. Blocking is symmetric, so equal types attack each other or neither;
    a knight shares no move with any other piece; a queen answers any K, R or B attack on it."""
    for a in range(n):
        for b in range(n):
            if a == b:
                continue
            ab, ba = (a, b) in arcs, (b, a) in arcs
            ta, tb = types[a], types[b]
            if ab and ba and (ta == "N") != (tb == "N"):
                return False
            if ab and not ba and (ta == tb or (tb == "Q" and ta in "KRB")):
                return False
    return True


def solve(arcs, n: int, types: str):
    arcs = set(arcs)
    pos = [(Int(f"x{i}"), Int(f"y{i}")) for i in range(n)]
    s = Solver()
    s.add(pos[0][0] == 0, pos[0][1] == 0)
    for i in range(n):
        for j in range(i + 1, n):
            s.add(Or(pos[i][0] != pos[j][0], pos[i][1] != pos[j][1]))
    for a in range(n):
        for b in range(n):
            if a != b:
                att = attacks(types[a], a, b, pos)
                s.add(att if (a, b) in arcs else Not(att))
    r = s.check()
    if r == sat:
        m = s.model()
        p = [(m.eval(x).as_long(), m.eval(y).as_long()) for x, y in pos]
        assert capture_graph(types, p) == arcs, (types, p)
        return "sat", p
    return ("unsat" if r == unsat else "unknown"), None


def decide(arcs, n: int):
    """Return (verdict, types, positions, number of Z3 calls)."""
    arcs = set(arcs)
    calls, unknown = 0, 0
    for types in map("".join, product(TYPES, repeat=n)):
        if not plausible(types, arcs, n):
            continue
        calls += 1
        r, p = solve(arcs, n, types)
        if r == "sat":
            return "REALIZABLE", types, p, calls
        unknown += r == "unknown"
    return ("UNKNOWN" if unknown else "NONE"), None, None, calls


def main() -> None:
    n = 6
    names = {canon(a, n): k for k, a in OPEN.items()}
    todo = sys.argv[1:] or [str(i) for i in range(len(all_classes(n)))]
    classes = all_classes(n)
    for key in todo:
        arcs = OPEN[key] if key in OPEN else sorted(classes[int(key)])
        label = (
            key
            if key in OPEN
            else f"class{key}"
            + (f"={names[classes[int(key)]]}" if classes[int(key)] in names else "")
        )
        t0 = time.time()
        v, types, p, calls = decide(arcs, n)
        print(
            f"{label}: {v} calls={calls} {time.time() - t0:.1f}s types={types} pos={p} arcs={sorted(arcs)}",
            flush=True,
        )


if __name__ == "__main__":
    main()
