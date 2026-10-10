"""Write figs/taxismall.tex: the placements for n = 3 and 4 (Golomb rulers on a line) and n = 6 (two adjacent lines),
distances verified here to be exactly 1..C(n,2)."""
from itertools import combinations
from pathlib import Path

P = {3: [(0, 0), (0, 2), (0, 3)], 4: [(0, 0), (0, 2), (0, 5), (0, 6)], 6: [(0, 0), (0, 14), (0, 15), (1, 4), (1, 6), (1, 12)]}
for n, pts in P.items():
    d = sorted(abs(a - c) + abs(b - e) for (a, b), (c, e) in combinations(pts, 2))
    assert d == list(range(1, n * (n - 1) // 2 + 1))
S = 0.42
out = []
for col, (n, pts) in enumerate(P.items()):
    x0 = col * 1.9
    w = 1 if n == 6 else 0
    for x in range(0, w + 1):
        out.append(rf"\draw[thin] ({x0+x*S:.3f},0) -- ({x0+x*S:.3f},{15*S:.3f});" if n == 6 else rf"\draw[thin] ({x0:.3f},0) -- ({x0:.3f},{6*S:.3f});")
    top = 15 if n == 6 else 6
    for yy in range(top + 1):
        out.append(rf"\draw[inkmuted!40] ({x0-0.06:.3f},{yy*S:.3f}) -- ({x0+w*S+0.06:.3f},{yy*S:.3f});")
    for (x, y) in pts:
        out.append(rf"\fill[{'copper' if (x+y)%2 else 'black'}] ({x0+x*S:.3f},{y*S:.3f}) circle (2.4pt);")
        out.append(rf"\node[{'left' if x == 0 else 'right'}, font=\tiny] at ({x0+x*S:.3f},{y*S:.3f}) {{$({x},{y})$}};")
    out.append(rf"\node[font=\small] at ({x0+w*S/2:.3f},-0.45) {{$n={n}$}};")
HERE = Path(__file__).resolve().parent
path = ((HERE.parent / "paper" / "figs") if (HERE.parent / "paper").exists() else (HERE.parent / "note" / "figs")) / "taxismall.tex"
path.write_text("\n".join(out) + "\n")
print("wrote", path)
