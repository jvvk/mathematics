"""Generate the paper's TikZ figures from the data in ../verify, checking each one as it is drawn.

Run from this directory: python3 make_figs.py   (standard library only)
"""

import importlib.util
import json
from pathlib import Path

HERE = Path(__file__).resolve().parent
VERIFY = HERE.parent / "verify"


def _load(name: str, path: Path):
    spec = importlib.util.spec_from_file_location(name, path)
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    return mod


bishops = _load("bishops_check", VERIFY / "bishops" / "check.py")
capture = _load("capture_check", VERIFY / "capture-digraphs" / "verify" / "check.py")

KING = [(dx, dy) for dx in (-1, 0, 1) for dy in (-1, 0, 1) if (dx, dy) != (0, 0)]


def fig_bishops() -> str:
    pos = json.loads((VERIFY / "bishops" / "positions.json").read_text())["6"]
    board = {(x, y): c for x, y, c in pos}
    assert bishops.counts(board) == [8, 8, 8] and bishops.attacks_ok(board, 6)
    fill = {1: "black", 2: "white", 3: "black!35"}
    out = [r"\begin{tikzpicture}[scale=0.62]"]
    for x in range(6):
        for y in range(6):
            shade = "black!8" if (x + y) % 2 else "white"
            out.append(rf"\fill[{shade}] ({x},{y}) rectangle ({x + 1},{y + 1});")
    out.append(r"\draw (0,0) grid (6,6);")
    for (x, y), c in board.items():
        out.append(
            rf"\filldraw[fill={fill[c]},draw=black,line width=0.6pt] ({x + 0.5},{y + 0.5}) circle (0.3);"
        )
    out.append(r"\end{tikzpicture}")
    return "\n".join(out)


def fig_touch() -> str:
    controls = json.loads((VERIFY / "touch-cycles" / "controls.json").read_text())
    ex = next(c for c in controls if c["triple"] == [1, 1, 6])
    cells = {(x, y): col for x, y, col in ex["cells"]}
    a, b, c = ex["triple"]
    need = {"A": ("B", a), "B": ("C", b), "C": ("A", c)}
    for (x, y), col in cells.items():
        target, k = need[col]
        assert sum(cells.get((x + dx, y + dy)) == target for dx, dy in KING) == k
    style = {"A": "fill=white", "B": "fill=black", "C": "fill=black!35"}
    xs = [p[0] for p in cells]
    ys = [p[1] for p in cells]
    out = [r"\begin{tikzpicture}[scale=0.55]"]
    out.append(
        rf"\draw[black!25] ({min(xs) - 0.5},{min(ys) - 0.5}) grid ({max(xs) + 1.5},{max(ys) + 1.5});"
    )
    for (x, y), col in cells.items():
        out.append(
            rf"\filldraw[{style[col]},draw=black,line width=0.6pt] ({x + 0.5},{y + 0.5}) circle (0.32);"
        )
    out.append(r"\end{tikzpicture}")
    return "\n".join(out)


def fig_capture() -> str:
    rows = [". . N", "R . K", "B R .", ". N ."]
    types, pos = "", []
    for r, row in enumerate(rows):
        for x, ch in enumerate(row.split()):
            if ch != ".":
                types += ch
                pos.append((x, len(rows) - 1 - r))
    arcs = capture.capture_graph(types, pos)
    for v in range(6):
        assert (
            sum(1 for p, _ in arcs if p == v) == 2
            and sum(1 for _, q in arcs if q == v) == 2
        )
    names = {
        "K": r"\symking",
        "Q": r"\symqueen",
        "R": r"\symrook",
        "B": r"\symbishop",
        "N": r"\symknight",
    }
    out = [r"\begin{tikzpicture}[scale=0.9]"]
    for x in range(3):
        for y in range(4):
            shade = "black!8" if (x + y) % 2 else "white"
            out.append(rf"\fill[{shade}] ({x},{y}) rectangle ({x + 1},{y + 1});")
    out.append(r"\draw (0,0) grid (3,4);")
    for p, q in sorted(arcs):
        (x1, y1), (x2, y2) = pos[p], pos[q]
        out.append(
            rf"\draw[-{{Stealth[length=5pt]}},black!60,line width=0.7pt,shorten >=9pt,shorten <=9pt,bend left=12] ({x1 + 0.5},{y1 + 0.5}) to ({x2 + 0.5},{y2 + 0.5});"
        )
    for t, (x, y) in zip(types, pos):
        out.append(rf"\node[font=\large] at ({x + 0.5},{y + 0.5}) {{{names[t]}}};")
    out.append(r"\end{tikzpicture}")
    return "\n".join(out)


def fig_q() -> str:
    arcs = [
        (0, 1),
        (0, 2),
        (1, 0),
        (1, 2),
        (2, 3),
        (2, 4),
        (3, 0),
        (3, 5),
        (4, 3),
        (4, 5),
        (5, 1),
        (5, 4),
    ]
    out = [r"\begin{tikzpicture}[scale=1.25]"]
    for v in range(6):
        out.append(
            rf"\node[circle,fill=black,inner sep=2.2pt] (v{v}) at ({90 + 60 * v}:1.25) {{}};"
        )
    for p, q in arcs:
        bend = ",bend left=14" if (q, p) in arcs else ""
        out.append(
            rf"\draw[-{{Stealth[length=6pt]}},line width=0.7pt,shorten >=3pt,shorten <=3pt{bend}] (v{p}) to (v{q});"
        )
    out.append(r"\end{tikzpicture}")
    return "\n".join(out)


def fig_heptomino() -> str:
    shape = [".##", ".#.", ".#.", ".#.", "##."]
    out = [r"\begin{tikzpicture}[scale=0.6]"]
    for r, row in enumerate(shape):
        y = len(shape) - 1 - r
        for x, ch in enumerate(row):
            if ch == "#":
                out.append(
                    rf"\filldraw[fill=black!18,draw=black] ({x},{y}) rectangle ({x + 1},{y + 1});"
                )
        out.append(rf"\node[font=\small] at (3.6,{y + 0.5}) {{{row.count('#')}}};")
    for x in range(3):
        out.append(
            rf"\node[font=\small] at ({x + 0.5},-0.45) {{{sum(row[x] == '#' for row in shape)}}};"
        )
    out.append(r"\end{tikzpicture}")
    return "\n".join(out)


if __name__ == "__main__":
    for name, fn in (
        ("bishops", fig_bishops),
        ("touch", fig_touch),
        ("capture", fig_capture),
        ("q", fig_q),
        ("heptomino", fig_heptomino),
    ):
        (HERE / f"fig_{name}.tex").write_text(fn() + "\n")
        print("wrote", f"fig_{name}.tex")
