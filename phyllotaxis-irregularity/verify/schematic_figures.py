"""TikZ for the schematic figures of the paper, from the exact rational models of the limiting tilings.

Points (X, Y) at modulus N stand for (X/sqrt N, sqrt3 Y/sqrt N) in units of the disk diameter (paper
Sec. 2.3; Lean Tilings.lean). Every front below is a word in the threshold vectors, so every tangency drawn
is exact. Writes ../paper/fig_front.tex, fig_step1.tex, fig_burst.tex.
"""

from __future__ import annotations

import math
import os

OUT = os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "paper")
Pt = tuple[float, float]


def real(p: Pt, N: int) -> complex:
    return complex(p[0] / math.sqrt(N), math.sqrt(3) * p[1] / math.sqrt(N))


def walk(vs: list[Pt]) -> list[Pt]:
    pts = [(0.0, 0.0)]
    for v in vs:
        pts.append((pts[-1][0] + v[0], pts[-1][1] + v[1]))
    return pts


def apex(a: complex, b: complex) -> complex:
    """Unit-diameter disk touching unit disks at a and b, above the segment a->b."""
    m, d = (a + b) / 2, b - a
    h = math.sqrt(max(1 - abs(d) ** 2 / 4, 0.0))
    return m + 1j * d / abs(d) * h


def panel(
    pts: list[complex],
    labels: list[str],
    new: list[complex],
    extra: str,
    dx: float,
    caption: str,
    period: float,
    dots: list[complex] = (),
) -> str:
    out = [f"\\begin{{scope}}[shift={{({dx:.3f},0)}}]"]
    allp = pts[:-1] + [p + period for p in pts[:1]]
    for p in allp:
        out.append(f"\\draw[fill=black!8] ({p.real:.4f},{p.imag:.4f}) circle (0.5);")
    for q in new:
        out.append(f"\\draw[thick] ({q.real:.4f},{q.imag:.4f}) circle (0.5);")
    for q in dots:
        out.append(
            f"\\draw[densely dotted,thick] ({q.real:.4f},{q.imag:.4f}) circle (0.5);"
        )
    for k in range(len(pts) - 1):
        a, b = pts[k], pts[k + 1]
        n = 1j * (b - a) / abs(b - a)
        m = (a + b) / 2 - 0.78 * n
        out.append(
            f"\\draw[-{{Latex[length=1.6mm]}}] ({a.real:.4f},{a.imag:.4f})--({b.real:.4f},{b.imag:.4f});"
        )
        if labels[k]:
            out.append(f"\\node[font=\\small] at ({m.real:.4f},{m.imag:.4f}) {{${labels[k]}$}};")
    out.append(extra)
    lo = min(p.imag for p in pts) - 1.15
    out.append(
        f"\\node[font=\\small,align=center,text width=5.2cm,anchor=north] at ({period / 2:.4f},{lo + 0.35:.4f}) {{{caption}}};"
    )
    out.append("\\end{scope}")
    return "\n".join(out)


def rot(v: Pt, sign: int) -> Pt:
    """Rotation by sign*60 degrees in the rational model."""
    x, y = v
    return (
        ((x - 3 * y) / 2, (x + y) / 2) if sign > 0 else ((x + 3 * y) / 2, (y - x) / 2)
    )


def step1() -> str:
    N = 7
    U, D = (2.5, 0.5), (2.0, -1.0)
    Up = rot(U, +1)
    per = 7 / math.sqrt(N)
    a = [real(p, N) for p in walk([D, U, U])]
    t1 = real((4.5 + Up[0], -0.5 + Up[1]), N)
    b = [real(p, N) for p in walk([U, D, D, Up])]  # word Ua Ub- D Ub+
    pent = apex(b[1], b[4])
    c = [real(p, N) for p in walk([Up, D, D, Up, D])]  # word Ua+ Ua- D Ub+ Ub-
    sh = per + 2.2
    s = [
        panel(
            a,
            ["D", "U_{\\mathrm a}", "U_{\\mathrm b}"],
            [t1],
            "",
            0.0,
            "(a) $(1,2)$ at threshold:\\\\first triangle on $U_{\\mathrm b}$",
            per,
        ),
        panel(
            b,
            ["", "U_{\\mathrm b}^-", "D", "U_{\\mathrm b}^+"],
            [],
            "",
            sh,
            "(b) $(2,2)$ phase: the triple\\\\$U_{\\mathrm b}^-,D,U_{\\mathrm b}^+$ (margin $\\sqrt7|c|$)",
            per,
            dots=[pent],
        ),
        panel(
            c,
            ["", "", "D", "", ""],
            [c[1]],
            "",
            2 * sh,
            "(c) second triangle, on $U_{\\mathrm a}$: front $(3,2)$ with steep ups $U_{\\mathrm a}^+$, $U_{\\mathrm b}^+$",
            per,
        ),
    ]
    return "\n".join(s)


def burst() -> str:
    N = 19
    D, U = (4.0, -1.0), (3.5, 1.5)
    S = rot(D, -1)
    per = 19 / math.sqrt(N)
    words = [
        (
            [D, D, U, D, U],
            ["D", "U_{\\mathrm a}^-", "U_{\\mathrm b}^+", "", "U_{\\mathrm a}^+"],
            "(a) $(3,2)$ at threshold",
            None,
            [],
        ),
        (
            [U, S, D, U, D, U],
            ["", "", "U_{\\mathrm a}^-", "U_{\\mathrm b}^+", "", "U_{\\mathrm a}^+"],
            "(b) triangle on $D$ (new vectors $D^+$, $D^-$)",
            1,
            [],
        ),
        (
            [U, S, D, U, U, D],
            ["", "", "U_{\\mathrm a}^-", "U_{\\mathrm b}^+", "U_{\\mathrm a}^+", ""],
            "(c) rhombus: $U_{\\mathrm b}^+$ meets $U_{\\mathrm a}^+$",
            5,
            [],
        ),
        (
            [U, S, U, S, U, U, D],
            ["", "", "", "", "U_{\\mathrm b}^+", "U_{\\mathrm a}^+", ""],
            "(d) triangle on $U_{\\mathrm a}^-$ gives a steep child; the pentagon $Q$ fits on it, $U_{\\mathrm b}^+$ and $U_{\\mathrm a}^+$",
            3,
            ["Q"],
        ),
    ]
    out = []
    for k, (vs, lab, cap, newidx, q) in enumerate(words):
        pts = [real(p, N) for p in walk(vs)]
        new = [pts[newidx]] if newidx is not None else []
        dots = [real((11.0, 2.0), N)] if q else []
        dx, dy = (k % 2) * (per + 1.6), -(k // 2) * 4.6
        out.append(f"\\begin{{scope}}[shift={{({dx:.3f},{dy:.3f})}}]")
        out.append(panel(pts, lab, new, "", 0.0, cap, per, dots=dots))
        if q:
            qq = dots[0]
            out.append(f"\\node at ({qq.real:.4f},{qq.imag:.4f}) {{$Q$}};")
        out.append("\\end{scope}")
    return "\n".join(out)


if __name__ == "__main__":
    for name, body in (("fig_step1.tex", step1()), ("fig_burst.tex", burst())):
        with open(os.path.join(OUT, name), "w") as f:
            f.write("% generated by verify/schematic_figures.py\n" + body + "\n")
        print("wrote", name)
