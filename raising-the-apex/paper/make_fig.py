"""Write fig_slices.tex: the base [-a, b] on the x-axis with foot D = 0, apexes (0, h) for three heights, the
standard Gaussian centred at MU (contours), a slice at height Y in two of the triangles, and each triangle's
Gaussian centroid computed by adaptive quadrature.

    ~/.venvs/main/bin/python make_fig.py
"""
from __future__ import annotations

import numpy as np
from scipy.integrate import dblquad

A, B = 1.2, 0.8
HS = [0.7, 1.2, 2.0]
MU = np.array([0.5, 0.6])
Y = 0.5


def centroid(h: float) -> tuple[float, float]:
    g = lambda x, y: np.exp(-((x - MU[0]) ** 2 + (y - MU[1]) ** 2) / 2)
    lo, hi = (lambda y: -A * (1 - y / h)), (lambda y: B * (1 - y / h))
    m = dblquad(lambda x, y: g(x, y), 0, h, lo, hi, epsabs=1e-12)[0]
    mx = dblquad(lambda x, y: x * g(x, y), 0, h, lo, hi, epsabs=1e-12)[0]
    my = dblquad(lambda x, y: y * g(x, y), 0, h, lo, hi, epsabs=1e-12)[0]
    return mx / m, my / m


cols = ["inkblue", "rust", "olive"]
out = ["\\begin{tikzpicture}[scale=2.6,line cap=round,line join=round]"]
for r in (0.4, 0.8, 1.2, 1.6):
    out.append(f"  \\draw[gray!30] ({MU[0]},{MU[1]}) circle ({r});")
out.append(f"  \\fill[gray!60] ({MU[0]},{MU[1]}) circle (0.6pt);")
for h, c in zip(HS, cols):
    out.append(f"  \\draw[{c},thick] ({-A},0) -- ({B},0) -- (0,{h}) -- cycle;")
for h, c in reversed(list(zip(HS[1:], cols[1:]))):
    s = 1 - Y / h
    out.append(f"  \\draw[{c},line width={'2.4pt' if h == HS[-1] else '1.2pt'}] ({-A * s:.4f},{Y}) -- ({B * s:.4f},{Y});")
out.append(f"  \\draw[gray,dotted] (-1.45,{Y}) node[left,font=\\scriptsize,black] {{height $y$}} -- (1.0,{Y});")
out.append(f"  \\draw[dashed,gray] (0,0) -- (0,{HS[-1]});")
out.append("  \\fill (0,0) circle (0.9pt) node[below,font=\\small] {$D$};")
out.append(f"  \\node[below,font=\\small] at ({-A},0) {{$A$}};")
out.append(f"  \\node[below,font=\\small] at ({B},0) {{$B$}};")
rows = []
for h, c in zip(HS, cols):
    x, y = centroid(h)
    rows.append((h, x, y))
    out.append(f"  \\fill[{c}] ({x:.4f},{y:.4f}) circle (1.3pt);")
    out.append(f"  \\node[{c},font=\\scriptsize,anchor=west] at (1.35,{y:.4f}) {{$h={h:g}$: height ${y:.3f}$}};")
    out.append(f"  \\draw[{c},densely dotted] ({x:.4f},{y:.4f}) -- (1.33,{y:.4f});")
out.append("\\end{tikzpicture}")
open("fig_slices.tex", "w").write("\n".join(out) + "\n")
for r in rows:
    print("h=%g centroid (%.6f, %.6f)" % r)
