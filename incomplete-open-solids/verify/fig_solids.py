"""Writes the TikZ figures of the note (paper/figs/*.tex): the graphs left after deleting unused vertices."""
from itertools import combinations
from pathlib import Path

OUT = Path(__file__).resolve().parent.parent / "paper" / "figs"


def cube_pos(v):
    x, y, z = v & 1, v >> 1 & 1, v >> 2 & 1
    return (1.5 * x + 0.65 * y, 1.5 * z + 0.5 * y)


def oct_pos(v):
    axis, sign = v // 2, 1 if v % 2 == 0 else -1
    return [(1.25 * sign, -0.12 * sign), (0.5 * sign, 0.38 * sign), (0, 1.3 * sign)][axis]


CUBE = [(a, b) for a, b in combinations(range(8), 2) if (a ^ b) in (1, 2, 4)]
OCT = [(a, b) for a, b in combinations(range(6), 2) if a // 2 != b // 2]


def panel(pos, edges, unused, shown, label, hub=None, accent=()):
    out = ["\\begin{tikzpicture}[scale=0.95]"]
    for a, b in edges:
        (x1, y1), (x2, y2) = pos(a), pos(b)
        if (a, b) in shown:
            col = "copper" if (a, b) in accent else "black"
            out.append(f"\\draw[line width=1.1pt,{col}] ({x1:.2f},{y1:.2f})--({x2:.2f},{y2:.2f});")
        else:
            out.append(f"\\draw[inkmuted!45,dashed,thin] ({x1:.2f},{y1:.2f})--({x2:.2f},{y2:.2f});")
    used = {v for e in shown for v in e}
    for v in sorted({v for e in edges for v in e}):
        x, y = pos(v)
        if v in unused:
            out.append(f"\\draw[inkmuted,fill=white] ({x:.2f},{y:.2f}) circle (2.4pt);")
        elif v in used:
            fill = "copper" if v == hub else "black"
            out.append(f"\\fill[{fill}] ({x:.2f},{y:.2f}) circle (2.2pt);")
    out.append(f"\\node[below,font=\\small] at (current bounding box.south) {{{label}}};")
    out.append("\\end{tikzpicture}")
    return "\n".join(out)


def keep(edges, unused):
    return {e for e in edges if not set(e) & set(unused)}


def main():
    OUT.mkdir(parents=True, exist_ok=True)
    cube = []
    for unused, label in [((0, 1), "(a) ladder"), ((0, 3), "(b) square with leaves"),
                          ((0, 7), "(c) hexagon"), ((0,), "(d) hexagon with hub")]:
        hub = 7 if unused == (0,) else None
        acc = {e for e in keep(CUBE, unused) if hub in e} if hub is not None else ()
        cube.append(panel(cube_pos, CUBE, unused, keep(CUBE, unused), label, hub, acc))
    (OUT / "cube_panels.tex").write_text("\n\\hfill\n".join(cube) + "\n")
    tri = {(0, 2), (0, 4), (2, 4), (1, 3), (1, 5), (3, 5)}
    lone = {(0, 2)} | {e for e in OCT if not set(e) & {0, 2}}
    octs = [panel(oct_pos, OCT, (5,), keep(OCT, (5,)), "(a) wheel", 4, {e for e in keep(OCT, (5,)) if 4 in e}),
            panel(oct_pos, OCT, (0, 2), keep(OCT, (0, 2)), "(b) $K_4$ minus an edge"),
            panel(oct_pos, OCT, (), tri, "(c) opposite triangles"),
            panel(oct_pos, OCT, (), lone, "(d) edge and five edges", accent={(0, 2)})]
    (OUT / "oct_panels.tex").write_text("\n\\hfill\n".join(octs) + "\n")
    print("wrote", *sorted(p.name for p in OUT.glob("*.tex")))


if __name__ == "__main__":
    main()
