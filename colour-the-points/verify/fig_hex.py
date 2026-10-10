"""Write figs/hex7.tex: the posted 7-colouring (side-1/2 hexagons, centres i x + j y, colour (j - 2i) mod 7) around the
origin; colour-0 hexagons shaded, witness points (0.45, 0) and (1.8, sqrt3/4) joined."""
import math
from pathlib import Path

R3 = math.sqrt(3)
x, y = (0.75, R3 / 4), (0.0, R3 / 2)
S = 1.6
lines = []
for i in range(-4, 6):
    for j in range(-5, 6):
        c = (i * x[0] + j * y[0], i * x[1] + j * y[1])
        if not (-1.6 < c[0] < 3.4 and -1.5 < c[1] < 1.9):
            continue
        pts = " -- ".join(f"({S * (c[0] + 0.5 * math.cos(math.pi * k / 3)):.3f},{S * (c[1] + 0.5 * math.sin(math.pi * k / 3)):.3f})" for k in range(6))
        if (j - 2 * i) % 7 == 0:
            lines.append(f"\\filldraw[fill=copper!35, draw=inkmuted, line width=0.3pt] {pts} -- cycle;")
        else:
            lines.append(f"\\draw[inkmuted!60, line width=0.3pt] {pts} -- cycle;")
p1, p2 = (0.45, 0.0), (1.8, R3 / 4)
lines.append(f"\\draw[thick] ({S * p1[0]:.3f},{S * p1[1]:.3f}) -- ({S * p2[0]:.3f},{S * p2[1]:.3f});")
for p in (p1, p2):
    lines.append(f"\\fill ({S * p[0]:.3f},{S * p[1]:.3f}) circle (1.8pt);")
HERE = Path(__file__).resolve().parent
out = ((HERE.parent / "paper" / "figs") if (HERE.parent / "paper").exists() else (HERE.parent / "note" / "figs")) / "hex7.tex"
out.write_text("\n".join(lines) + "\n")
print("wrote", out, len(lines))
