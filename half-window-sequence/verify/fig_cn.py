"""Write book/figs/cn64.tex: points (n, c_n) for n <= 64 in TikZ coordinates (x = n/8, y = 2(c_n - 1))."""
from fractions import Fraction
from pathlib import Path

a = [None, Fraction(1)]
for n in range(2, 65):
    a.append(a[-1] if n % 2 == 0 else a[-1] - a[(n - 1) // 2] / n)
c = [None] + [n * a[n] for n in range(1, 65)]
assert all((c[n] > c[n - 1]) == (n % 2 == 0) for n in range(3, 65))  # the caption: up at even, down at odd steps
pts = [(n / 8, 2 * (float(c[n]) - 1)) for n in range(1, 65)]
path = " -- ".join(f"({x:.3f},{y:.3f})" for x, y in pts)
dots = "\n".join(f"\\fill ({x:.3f},{y:.3f}) circle (0.9pt);" for x, y in pts)
out = Path(__file__).resolve().parents[1] / "paper" / "figs" / "cn64.tex"
out.write_text(f"\\draw[book/thin] {path};\n{dots}\n")
print("wrote", out)
