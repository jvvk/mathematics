"""Write out/smaller_boards.json: positions on smaller boards than the published ones, each checked
to realize the same digraph class as Friedman's published position (out/published_solutions.txt)."""

from __future__ import annotations

import json
import sys
from pathlib import Path

from digraphs import canon

ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT / "verify"))
from check import capture_graph  # noqa: E402

FOUND = {  # from out/min_boards.log (cvc5 search in src/min_board.py), rows top to bottom
    "h": ["Q..", "K.N", "N.K", "..Q"],
    "k": ["R.R", "...", "KNK", ".B."],
    "l": [".RK", "..R", "..N", "QK."],
}


# Friedman's drawings of h, k, l (figures a6-2-h/k/l), read by hand; each reading is checked to be
# the class of the published position. Vertex coordinates reproduce his layout.
HEX = [(-1, 1.73), (1, 1.73), (2, 0), (1, -1.73), (-1, -1.73), (-2, 0)]
PENT = [(0, 2), (1.9, 0.62), (1.18, -1.62), (-1.18, -1.62), (-1.9, 0.62), (0, 0)]  # T, UR, LR, LL, UL, centre
DIAGRAM = {
    "h": (HEX, [(0, 1), (1, 0), (0, 5), (5, 4), (4, 0), (4, 3), (3, 4), (1, 3), (3, 2), (2, 1), (5, 2), (2, 5)]),
    "k": (PENT, [(0, 4), (4, 0), (0, 1), (1, 0), (4, 5), (1, 5), (5, 3), (5, 2), (3, 2), (2, 3), (3, 4), (2, 1)]),
    "l": (PENT, [(0, 4), (4, 0), (0, 1), (1, 0), (4, 5), (5, 1), (5, 3), (2, 5), (3, 2), (2, 3), (3, 4), (1, 2)]),
}


def iso(src, dst, n: int = 6):
    """A bijection f with (a, b) in src iff (f(a), f(b)) in dst."""
    from itertools import permutations
    for p in permutations(range(n)):
        if {(p[a], p[b]) for a, b in src} == set(dst):
            return p
    return None


def parse(rows):
    h = len(rows)
    pieces = [(ch, c, h - 1 - r) for r, row in enumerate(rows) for c, ch in enumerate(row) if ch != "."]
    types = "".join(p[0] for p in pieces)
    return types, [(x, y) for _, x, y in pieces]


def main() -> None:
    pub = {}
    for ln in (ROOT / "out/published_solutions.txt").read_text().splitlines():
        if ln.strip() and not ln.startswith("#"):
            k, *rows = ln.split()
            pub[k] = rows
    out = {}
    for k, rows in FOUND.items():
        new = capture_graph(*parse(rows))
        old = capture_graph(*parse(pub[k]))
        assert canon(new, 6) == canon(old, 6), k
        layout, arcs = DIAGRAM[k]
        assert canon(arcs, 6) == canon(old, 6), f"misread diagram {k}"
        types, pos = parse(rows)
        f = iso(new, arcs)
        vertices = [None] * 6
        for piece_index, v in enumerate(f):
            x, y = pos[piece_index]
            vertices[v] = {"piece": types[piece_index], "square": "abcdefgh"[x] + str(y + 1)}
        assert capture_graph(types, pos) == {(f.index(a), f.index(b)) for a, b in arcs}
        out[k] = {
            "diagram_arcs": arcs,
            "diagram_xy": layout,
            "diagram_vertices": vertices,
            "rows_top_to_bottom": rows,
            "board": f"{len(rows[0])}x{len(rows)}",
            "published_rows": pub[k],
            "published_board": f"{len(pub[k][0])}x{len(pub[k])}",
        }
    (ROOT / "out/smaller_boards.json").write_text(json.dumps(out, indent=1) + "\n")
    print({k: (v["published_board"], v["board"]) for k, v in out.items()})


if __name__ == "__main__":
    main()
