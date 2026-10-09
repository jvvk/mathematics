"""Draw the twenty-vertex graph (K4 with each vertex replaced by K_{2,3}) as TikZ, with a Hamiltonian
cycle and an odd 9-cycle, using the same vertex labels and partner rule as the Lean file.

Run from this directory: python3 make_fig.py   (standard library only)
"""

import math
from pathlib import Path

CENTRES = {0: (-3.0, 3.0), 1: (3.0, 3.0), 2: (3.0, -3.0), 3: (-3.0, -3.0)}


def partner(v: int, i: int) -> tuple[int, int]:
    return ((v + (i + 3) % 4) % 4, (6 - i) % 5)


def adjacent(x: tuple[int, int], y: tuple[int, int]) -> bool:
    (v, i), (w, j) = x, y
    if v == w:
        return (i < 2) != (j < 2)
    return i >= 2 and j >= 2 and partner(v, i) == y


def position(v: int, i: int) -> tuple[float, float]:
    cx, cy = CENTRES[v]
    if i >= 2:
        w = partner(v, i)[0]
        dx, dy = CENTRES[w][0] - cx, CENTRES[w][1] - cy
        d = math.hypot(dx, dy)
        return cx + 1.5 * dx / d, cy + 1.5 * dy / d
    # inner vertices: either side of the block centre, across from the attachments' mean direction
    ax = sum(position(v, j)[0] for j in (2, 3, 4)) / 3 - cx
    ay = sum(position(v, j)[1] for j in (2, 3, 4)) / 3 - cy
    d = math.hypot(ax, ay)
    px, py = -ay / d, ax / d
    s = 0.85 if i == 0 else -0.85
    return cx - 0.45 * ax / d + s * px, cy - 0.45 * ay / d + s * py


HAM = [(v, i) for v in range(4) for i in (4, 0, 3, 1, 2)]
ODD = [(0, 3), (0, 0), (0, 2), (1, 4), (1, 0), (1, 2), (2, 4), (2, 0), (2, 3)]


def cycle_edges(cyc: list[tuple[int, int]]) -> set[frozenset]:
    edges = {frozenset((cyc[k], cyc[(k + 1) % len(cyc)])) for k in range(len(cyc))}
    assert all(adjacent(*tuple(e)) for e in edges) and len(set(cyc)) == len(cyc)
    return edges


def tikz(highlight: set[frozenset], colour: str) -> str:
    verts = [(v, i) for v in range(4) for i in range(5)]
    assert all(sum(adjacent(x, y) for y in verts if y != x) == 3 for x in verts)
    out = [r"\begin{tikzpicture}[scale=0.62]"]
    done = set()
    for x in verts:
        for y in verts:
            e = frozenset((x, y))
            if x != y and adjacent(x, y) and e not in done:
                done.add(e)
                (x1, y1), (x2, y2) = position(*x), position(*y)
                style = (
                    f"{colour},line width=2.2pt"
                    if e in highlight
                    else "black!35,line width=0.6pt"
                )
                out.append(
                    rf"\draw[{style}] ({x1:.3f},{y1:.3f}) -- ({x2:.3f},{y2:.3f});"
                )
    for x in verts:
        px, py = position(*x)
        fill = "white" if x[1] < 2 else "black"
        out.append(
            rf"\filldraw[fill={fill},draw=black] ({px:.3f},{py:.3f}) circle (0.13);"
        )
    out.append(r"\end{tikzpicture}")
    return "\n".join(out)


if __name__ == "__main__":
    here = Path(__file__).resolve().parent
    (here / "fig_ham.tex").write_text(tikz(cycle_edges(HAM), "orange!80!black") + "\n")
    (here / "fig_odd.tex").write_text(tikz(cycle_edges(ODD), "blue!70!black") + "\n")
    print("wrote fig_ham.tex and fig_odd.tex (graph cubic, both cycles valid)")
