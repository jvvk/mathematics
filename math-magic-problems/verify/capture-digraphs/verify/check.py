"""Independent checker: simulate a chess position square by square and return its capture digraph.
Shares no code with src/realize.py. Colour is ignored; a slider stops at the first piece it meets.

check(types, pos) -> set of arcs (a, b) meaning piece a attacks piece b.
"""

from __future__ import annotations

STEPS = {
    "K": [(dx, dy) for dx in (-1, 0, 1) for dy in (-1, 0, 1) if (dx, dy) != (0, 0)],
    "N": [(1, 2), (2, 1), (-1, 2), (-2, 1), (1, -2), (2, -1), (-1, -2), (-2, -1)],
}
RAYS = {
    "R": [(1, 0), (-1, 0), (0, 1), (0, -1)],
    "B": [(1, 1), (1, -1), (-1, 1), (-1, -1)],
}
RAYS["Q"] = RAYS["R"] + RAYS["B"]


def capture_graph(types: str, pos: list[tuple[int, int]]) -> set[tuple[int, int]]:
    if len(set(pos)) != len(pos):
        raise ValueError("two pieces on one square")
    at = {p: i for i, p in enumerate(pos)}
    xs = [p[0] for p in pos]
    ys = [p[1] for p in pos]
    reach = max(max(xs) - min(xs), max(ys) - min(ys)) + 1
    arcs = set()
    for a, (t, (x, y)) in enumerate(zip(types, pos)):
        if t in STEPS:
            for dx, dy in STEPS[t]:
                if (x + dx, y + dy) in at:
                    arcs.add((a, at[(x + dx, y + dy)]))
        else:
            for dx, dy in RAYS[t]:
                for k in range(1, reach + 1):
                    sq = (x + k * dx, y + k * dy)
                    if sq in at:
                        arcs.add((a, at[sq]))
                        break
    return arcs


def board(types: str, pos: list[tuple[int, int]]) -> str:
    x0 = min(p[0] for p in pos)
    y0 = min(p[1] for p in pos)
    w = max(p[0] for p in pos) - x0 + 1
    h = max(p[1] for p in pos) - y0 + 1
    g = [["." for _ in range(w)] for _ in range(h)]
    for t, (x, y) in zip(types, pos):
        g[h - 1 - (y - y0)][x - x0] = t
    return f"{w}x{h}\n" + "\n".join("".join(r) for r in g)
