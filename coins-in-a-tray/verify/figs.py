"""Figure data for the note (written to ../paper/figs if it exists, else note/figs).

rim.tex: (a) two rim coins 1/2 and 1/4 touching each other and the tray, with the angle alpha_3 at the centre;
         (b) the asker's n = 4 ring 1/3, 1/2, 1/4, 1/4, 1/2, built from the angles and checked to close up;
         (c) n = 5: a 1/5 coin must sit between two 1/2 coins at 60 degrees each, which puts them 120 degrees apart,
             where they overlap.
corona.tex: (a) the exact corona of a 1/7 coin by 1/2, 1/2, 1/4, 1/4, checked to close up;
            (b) the corona of a 1/5 coin by six 1/5 coins.
"""
import math
from pathlib import Path

HERE = Path(__file__).resolve().parent
OUT = (HERE.parent / "paper" / "figs") if (HERE.parent / "paper").exists() else (HERE / "note" / "figs")
S = 1.6  # tray radius in cm


def alpha(j, k):
    return 2 * math.asin(1 / math.sqrt((j - 1) * (k - 1)))


def ring(seq):
    """Centres (angle, radius) of rim coins placed in order, each tangent to the previous."""
    th, out = 0.0, []
    for i, j in enumerate(seq):
        out.append((th, j))
        th += alpha(j, seq[(i + 1) % len(seq)])
    return out, th


def coin(th, j, style):
    r = 1 / j
    x, y = (1 - r) * math.cos(th) * S, (1 - r) * math.sin(th) * S
    return rf"\draw[{style}] ({x:.3f},{y:.3f}) circle ({r * S:.3f});"


def panel(dx, body, label):
    return ([rf"\begin{{scope}}[shift={{({dx},0)}}]", rf"\draw[thick] (0,0) circle ({S});"] + body
            + [rf"\node[below, font=\small] at (0,{-S - 0.1}) {{{label}}};", r"\end{scope}"])


# (a)
A = [coin(math.pi / 2, 2, "fill=copper!25"), coin(math.pi / 2 + alpha(2, 4), 4, "fill=copper!25"),
     rf"\fill (0,0) circle (0.9pt);"]
for th, j in ((math.pi / 2, 2), (math.pi / 2 + alpha(2, 4), 4)):
    r = 1 - 1 / j
    A.append(rf"\draw[inkmuted] (0,0) -- ({r * math.cos(th) * S:.3f},{r * math.sin(th) * S:.3f});")
A.append(rf"\draw[inkmuted] ({0.35 * math.cos(math.pi / 2):.3f},{0.35:.3f}) arc (90:{90 + math.degrees(alpha(2, 4)):.2f}:0.35);")
A.append(rf"\node[font=\scriptsize] at ({0.55 * math.cos(math.pi / 2 + alpha(2, 4) / 2):.3f},"
         rf"{0.55 * math.sin(math.pi / 2 + alpha(2, 4) / 2):.3f}) {{$\alpha_3$}};")
# (b)
seq = [3, 2, 4, 4, 2]
cs, tot = ring(seq)
assert abs(tot - 2 * math.pi) < 1e-12
B = [coin(th + math.pi / 2, j, "fill=copper!25") for th, j in cs]
# (c)
C = [coin(math.pi / 2, 5, "fill=copper!25"), coin(math.pi / 2 + alpha(5, 2), 2, "fill=copper!12"),
     coin(math.pi / 2 - alpha(5, 2), 2, "fill=copper!12")]
assert abs(alpha(5, 2) - math.pi / 3) < 1e-12
d = 2 * 0.5 * math.sin(alpha(5, 2))  # centres of the two halves, at radius 1/2, 120 degrees apart
assert abs(d - math.sqrt(3) / 2) < 1e-12 and d < 1
OUT.mkdir(parents=True, exist_ok=True)
(OUT / "rim.tex").write_text("\n".join(panel(0, A, "(a)") + panel(4, B, "(b)") + panel(8, C, "(c)")) + "\n")
print("wrote", OUT / "rim.tex")


def corona_panel(dx, m, seq, label):
    """Coin 1/m at the origin with neighbours seq in cyclic order, each tangent to it and to the next."""
    r0, th, body = 1 / m, 0.0, []
    for i, j in enumerate(seq):
        k = seq[(i + 1) % len(seq)]
        a, b, c = r0 + 1 / j, r0 + 1 / k, 1 / j + 1 / k
        body.append((th, j))
        th += math.acos((a * a + b * b - c * c) / (2 * a * b))
    assert abs(th - 2 * math.pi) < 1e-12, (m, seq, th)
    out = [rf"\begin{{scope}}[shift={{({dx},0)}}]"]
    for t, j in body:
        d = (r0 + 1 / j) * S
        out.append(rf"\draw[fill=copper!12] ({d * math.cos(t + math.pi / 2):.3f},{d * math.sin(t + math.pi / 2):.3f})"
                   rf" circle ({S / j:.3f});")
    out.append(rf"\draw[fill=copper!40] (0,0) circle ({r0 * S:.3f});")
    out += [rf"\node[below, font=\small] at (0,{-1.25 * S:.3f}) {{{label}}};", r"\end{scope}"]
    return out


(OUT / "corona.tex").write_text("\n".join(corona_panel(0, 7, [2, 2, 4, 4], "(a)")
                                          + corona_panel(4.5, 5, [5] * 6, "(b)")) + "\n")
print("wrote", OUT / "corona.tex")
