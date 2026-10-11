"""Writes the note's TikZ figures to paper/figs/:
polygon.tex: the regular n-gon (n = 9 and n = 31) with all diagonals; the edge triangle in blue, the certified larger
             cell in copper.
tangent.tex: the rational-tangent mechanism: f(phi) = b g(phi) - a phi near its minimum, a level line, and the
             lattice of admissible (phi, d) points spaced 2bt, with the two points straddling the left root."""

import math
from pathlib import Path

import largest_cell as L

OUT = Path(__file__).resolve().parent.parent / "paper" / "figs"


def polygon_panel(n, scale, label):
    t = math.pi / n
    R = 1 / (2 * math.sin(t))
    P = [(R * math.cos(2 * k * t), R * math.sin(2 * k * t)) for k in range(n)]
    s = scale / R
    out = [f"\\begin{{tikzpicture}}[scale={s:.4f}]"]
    for i in range(n):
        for j in range(i + 1, n):
            (x1, y1), (x2, y2) = P[i], P[j]
            w = "0.15pt" if n > 20 else "0.4pt"
            out.append(
                f"\\draw[inkmuted,line width={w}] ({x1:.4f},{y1:.4f})--({x2:.4f},{y2:.4f});"
            )
    best, _, _ = L.best_cell(n)
    cells, _, _ = L.float_cells(n)
    # edge triangle on the side P0 P1
    mid = ((P[0][0] + P[1][0]) / 2, (P[0][1] + P[1][1]) / 2)
    edge = min(
        (c for c in cells if c.area > 0),
        key=lambda c: c.centroid.distance(L.Point(*mid)),
    )
    for poly, col in ((edge, "blue!60!black"), (best, "copper")):
        pts = " -- ".join(
            f"({x:.4f},{y:.4f})" for x, y in list(poly.exterior.coords)[:-1]
        )
        out.append(f"\\fill[{col},opacity=0.85] {pts} -- cycle;")
    out.append(f"\\node[below] at (0,{-R * 1.02:.3f}) {{\\small {label}}};")
    out.append("\\end{tikzpicture}")
    return "\n".join(out)


def tangent_panel():
    # an illustrative instance: rho = 0.6, a/b = 1/2 (rescaled picture, not to scale in t)
    rho, a, b, t = 0.6, 1, 2, 0.035
    g = lambda p: math.acos(rho * math.cos(p))
    f = lambda p: b * g(p) - a * p
    # minimum of f
    lo, hi = 0.2, 1.4
    for _ in range(80):
        m1, m2 = lo + (hi - lo) / 3, hi - (hi - lo) / 3
        if f(m1) < f(m2):
            hi = m2
        else:
            lo = m1
    p0 = (lo + hi) / 2
    w = 0.32
    level = max(f(p0 - w), f(p0 + w)) + 0.01
    sx, sy = 9.0, 40.0
    X = lambda p: (p - (p0 - 0.55)) * sx
    Y = lambda v: (v - f(p0) + 0.02) * sy
    out = ["\\begin{tikzpicture}[font=\\small]"]
    pts = " ".join(
        f"({X(p0 - 0.55 + k * 1.1 / 120):.3f},{Y(f(p0 - 0.55 + k * 1.1 / 120)):.3f})"
        for k in range(121)
    )
    out.append(f"\\draw[thick] plot[smooth] coordinates {{{pts}}};")
    out.append(
        f"\\draw[inkmuted,dashed] ({X(p0 - 0.55):.3f},{Y(level):.3f}) -- ({X(p0 + 0.55):.3f},{Y(level):.3f});"
    )
    out.append(
        f"\\node[anchor=west,inkmuted] at ({X(p0 + 0.55):.3f},{Y(level):.3f}) {{$\\ell$}};"
    )
    out.append(
        f"\\node[anchor=south] at ({X(p0 + 0.45):.3f},{Y(f(p0 + 0.45)) + 0.1:.3f}) {{$f(\\varphi)$}};"
    )
    # left root
    lo, hi = p0 - 0.55, p0
    for _ in range(80):
        mid = (lo + hi) / 2
        if f(mid) > level:
            lo = mid
        else:
            hi = mid
    root = (lo + hi) / 2
    out.append(
        f"\\draw[inkmuted] ({X(root):.3f},{Y(level) - 0.15:.3f}) -- ({X(root):.3f},{Y(level) + 0.15:.3f});"
    )
    # lattice points on the level line, spacing 2bt (exaggerated)
    sp = 2 * b * t * 1.6
    k0 = math.floor((root - (p0 - 0.55)) / sp)
    for k in range(int(1.1 / sp) + 1):
        p = p0 - 0.55 + k * sp
        inside = f(p) < level
        col = "copper" if k in (k0, k0 + 1) else ("black" if inside else "inkmuted")
        out.append(f"\\fill[{col}] ({X(p):.3f},{Y(level):.3f}) circle ({2.6 if col == 'copper' else 1.5}pt);")
    out.append(
        f"\\node[below,font=\\scriptsize] at ({X(root):.3f},{Y(level) - 0.2:.3f}) {{root}};"
    )
    out.append(
        f"\\draw[<->,inkmuted] ({X(p0 - 0.55 + k0 * sp):.3f},{Y(level) + 0.45:.3f}) -- "
        f"({X(p0 - 0.55 + (k0 + 1) * sp):.3f},{Y(level) + 0.45:.3f}) node[midway,above,font=\\scriptsize] {{$2bt$}};"
    )
    out.append(
        f"\\fill ({X(p0):.3f},{Y(f(p0)):.3f}) circle (1.2pt) node[below] {{$\\varphi_0$}};"
    )
    out.append("\\end{tikzpicture}")
    return "\n".join(out)


def main():
    OUT.mkdir(parents=True, exist_ok=True)
    (OUT / "polygon.tex").write_text(
        polygon_panel(9, 2.6, "$n=9$")
        + "\n\\hspace{1.2em}\n"
        + polygon_panel(31, 2.6, "$n=31$")
        + "\n"
    )
    (OUT / "tangent.tex").write_text(tangent_panel() + "\n")
    print("wrote polygon.tex, tangent.tex")


if __name__ == "__main__":
    main()
