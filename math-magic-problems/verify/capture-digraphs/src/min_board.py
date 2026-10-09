"""Smallest board (by area, then width) on which a class is realizable, using the cvc5 model of
verify/second.py with every piece confined to a w x h box. Usage: min_board.py class_index"""

from __future__ import annotations

import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent.parent / "verify"))
import second  # noqa: E402
from check import board, capture_graph  # noqa: E402
from cvc5.pythonic import Int, Not, Or, Solver, sat  # noqa: E402
from digraphs import all_classes  # noqa: E402


def fits(arcs, n: int, w: int, h: int):
    P = [(Int(f"x{i}"), Int(f"y{i}")) for i in range(n)]
    T = [Int(f"t{i}") for i in range(n)]
    s = Solver()
    for i in range(n):
        s.add(P[i][0] >= 0, P[i][0] < w, P[i][1] >= 0, P[i][1] < h, T[i] >= 0, T[i] <= 4)
        for j in range(i + 1, n):
            s.add(Or(P[i][0] != P[j][0], P[i][1] != P[j][1]))
    for a in range(n):
        for b in range(n):
            if a != b:
                e = second.attack(P, T, a, b)
                s.add(e if (a, b) in arcs else Not(e))
    if s.check() != sat:
        return None
    m = s.model()
    types = "".join("KQRBN"[m[v].as_long()] for v in T)
    pos = [(m[x].as_long(), m[y].as_long()) for x, y in P]
    assert capture_graph(types, pos) == arcs
    return types, pos


def main() -> None:
    arcs = set(all_classes(6)[int(sys.argv[1])])
    boards = sorted((w * h, w, h) for w in range(1, 9) for h in range(w, 65) if 6 <= w * h <= 64)
    for area, w, h in boards:
        r = fits(arcs, 6, w, h) or fits(arcs, 6, h, w)
        print(f"{w}x{h}: {'yes' if r else 'no'}", flush=True)
        if r:
            print(board(*r))
            return


if __name__ == "__main__":
    main()
