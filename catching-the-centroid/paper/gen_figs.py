"""Write the TikZ figures of note.tex (fig_*.tex) from computed data (core.py)."""
from __future__ import annotations

import sys
from pathlib import Path

import numpy as np

sys.path.insert(0, str(Path(__file__).resolve().parent.parent / "verify"))
from core import half_plane_b, regular  # noqa: E402

OUT = Path(__file__).resolve().parent
TRI = regular(3)  # centroid at the origin, circumradius 1


def poly(V: np.ndarray, style: str) -> str:
    return rf"\draw[{style}] " + " -- ".join(f"({x:.4f},{y:.4f})" for x, y in V) + " -- cycle;"


def fig_setup() -> str:
    """Equilateral triangle, centroid G, point X, the half-plane of good Y, a circle on XY through G's side."""
    s = 2.2
    V = TRI * s
    X = np.array([0.95, 0.35]) * s * 0.55
    u = X / np.linalg.norm(X)
    # far half-plane {y : y.u <= 0} clipped to the triangle
    pts = []
    for j in range(3):
        p, q = V[j], V[(j + 1) % 3]
        sp, sq = p @ u, q @ u
        if sp <= 0:
            pts.append(p)
        if sp * sq < 0:
            pts.append(p + (q - p) * sp / (sp - sq))
    H = np.array(pts)
    Y = np.array([-0.42, -0.30]) * s * 0.75
    C, R = (X + Y) / 2, np.linalg.norm(X - Y) / 2
    perp = np.array([-u[1], u[0]]) * 2.6
    L = [
        r"\begin{tikzpicture}[scale=1]",
        poly(H, "fill=softblue,draw=none"),
        poly(V, "thick,inkblue"),
        rf"\draw[gray,dashed] ({-perp[0]:.3f},{-perp[1]:.3f}) -- ({perp[0]:.3f},{perp[1]:.3f});",
        rf"\draw[rust,thick] ({C[0]:.4f},{C[1]:.4f}) circle ({R:.4f});",
        rf"\draw[rust] ({X[0]:.4f},{X[1]:.4f}) -- ({Y[0]:.4f},{Y[1]:.4f});",
        rf"\draw[gray] (0,0) -- ({X[0]:.4f},{X[1]:.4f}) (0,0) -- ({Y[0]:.4f},{Y[1]:.4f});",
        r"\fill (0,0) circle (1.5pt) node[above left=1pt] {$G$};",
        rf"\fill[rust] ({X[0]:.4f},{X[1]:.4f}) circle (1.6pt) node[right=2pt] {{$X$}};",
        rf"\fill[rust] ({Y[0]:.4f},{Y[1]:.4f}) circle (1.6pt) node[below=2pt] {{$Y$}};",
        r"\end{tikzpicture}",
    ]
    return "\n".join(L)


def curve(V: np.ndarray, scale: float, step: int = 16) -> list[str]:
    t, rho, b = half_plane_b(V, 8192)
    x, y = b, np.roll(b, -8192 // 4)
    pts = " -- ".join(f"({scale * x[i]:.3f},{scale * y[i]:.3f})" for i in range(0, len(x), step))
    return [rf"\draw[inkblue,thick] {pts} -- cycle;"]


def fig_curve() -> str:
    sc = 30.0
    m = sc / 18
    pent = np.array([[0, 0], [3, 0], [3.5, 1], [1, 2.2], [-0.4, 1.0]])
    L = [r"\begin{tikzpicture}"]
    for dx, V, lab in ((0.0, TRI, "equilateral triangle"), (4.6, pent, "a pentagon")):
        L.append(rf"\begin{{scope}}[xshift={dx}cm]")
        L.append(rf"\draw[gray!50] (-2,0) -- (2,0) (0,-2) -- (0,2);")
        L.append(rf"\draw[gray,dashed] ({-m:.3f},{-m:.3f}) rectangle ({m:.3f},{m:.3f});")
        L += curve(V, sc)
        L.append(rf"\node[below] at (0,-2.05) {{\small {lab}}};")
        L.append(r"\end{scope}")
    L.append(r"\end{tikzpicture}")
    return "\n".join(L)


def fig_hexagon() -> str:
    s = 2.0
    V = TRI * s
    W = -V
    # hexagon K cap (-K): intersection points of the sides
    H = []
    for j in range(3):
        p, q = V[j], V[(j + 1) % 3]
        for t in (1 / 3, 2 / 3):
            H.append(p + t * (q - p))
    H = np.array(H)
    ang = np.arctan2(H[:, 1], H[:, 0])
    H = H[np.argsort(ang)]
    L = [r"\begin{tikzpicture}", poly(V, "fill=rust!18,draw=none"), poly(H, "fill=softblue,draw=none")]
    for k in range(3):  # the three lines through G and antipodal crossing points
        p = H[k] * 1.55
        L.append(rf"\draw[gray] ({-p[0]:.3f},{-p[1]:.3f}) -- ({p[0]:.3f},{p[1]:.3f});")
    L += [poly(V, "thick,inkblue"), poly(W, "thick,inkblue,dashed"), r"\fill (0,0) circle (1.4pt);",
          rf"\node at ({V[0][0] * 0.78:.3f},{V[0][1] * 0.78 + 0.0:.3f}) {{\small cap}};",
          rf"\node[inkblue] at ({V[1][0] + 0.25:.3f},{V[1][1] + 0.1:.3f}) {{$K$}};",
          rf"\node[inkblue] at ({W[0][0] - 0.35:.3f},{W[0][1]:.3f}) {{$-K$}};",
          r"\end{tikzpicture}"]
    return "\n".join(L)


if __name__ == "__main__":
    for name, f in (("fig_setup", fig_setup), ("fig_curve", fig_curve), ("fig_hexagon", fig_hexagon)):
        (OUT / f"{name}.tex").write_text(f() + "\n")
        print("wrote", name)
