"""Write book/figs/window24.tex: bars a_k for k = 1..24 (exact rationals), the window W_24 = {12,...,23} in copper, the bar
a_24 hatched. Lemma 4.2: 24 a_24 = 1 + sum of the copper bars (checked here exactly)."""

from fractions import Fraction
from pathlib import Path

a = [None, Fraction(1)]
for n in range(2, 25):
    a.append(a[-1] if n % 2 == 0 else a[-1] - a[(n - 1) // 2] / n)
n = 24
W = range((n + 1) // 2, n)
assert n * a[n] == 1 + sum(a[k] for k in W)
SX, SY, BW = 0.34, 2.4, 0.24
out = [rf"\draw[book/thin] (0,0) -- ({(n + 0.8) * SX:.3f},0);"]
for k in range(1, n + 1):
    x = k * SX
    col = "copper" if k in W else ("inkmuted!45" if k != n else "white")
    extra = ", draw=black, pattern=north east lines" if k == n else ""
    out.append(
        rf"\fill[{col}] ({x - BW / 2:.3f},0) rectangle ({x + BW / 2:.3f},{float(a[k]) * SY:.3f});"
        if k != n
        else rf"\draw ({x - BW / 2:.3f},0) rectangle ({x + BW / 2:.3f},{float(a[k]) * SY:.3f});"
    )
for k in (1, 6, 12, 18, 24):
    out.append(rf"\node[below, font=\scriptsize] at ({k * SX:.3f},0) {{{k}}};")
x1, x2 = 12 * SX - BW / 2, 23 * SX + BW / 2
out.append(
    rf"\draw[copper] ({x1:.3f},-0.36) -- ({x1:.3f},-0.44) -- ({x2:.3f},-0.44) -- ({x2:.3f},-0.36);"
)
out.append(
    rf"\node[below, font=\scriptsize] at ({(x1 + x2) / 2:.3f},-0.44) {{window $12\le k<24$}};"
)
out.append(
    rf"\node[above, font=\scriptsize] at ({n * SX:.3f},{float(a[n]) * SY:.3f}) {{$a_{{24}}$}};"
)
out.append(
    rf"\node[above, font=\scriptsize] at ({1.5 * SX:.3f},{SY:.3f}) {{$a_1=a_2=1$}};"
)
path = Path(__file__).resolve().parents[1] / "paper" / "figs" / "window24.tex"
path.write_text("\n".join(out) + "\n")
print("wrote", path, "24 a_24 =", n * a[n], "=", float(n * a[n]))
