"""Write figs/sevenproof.tex: (a) the extreme case of Lemma 12.1; (b) the lowest point P with six neighbours in the upper
half-annulus 1 < r <= sqrt3, directions 35 degrees apart (pairwise distances > 1, checked here)."""
import math
from itertools import combinations
from pathlib import Path

R3 = math.sqrt(3)
S = 1.25
L = []
# panel (a), origin at (0,0)
L.append(r"\begin{scope}")
L.append(rf"\fill[copper!15] (0:{S:.3f}) arc (0:30:{S:.3f}) -- (30:{S*R3:.3f}) arc (30:0:{S*R3:.3f}) -- cycle;")
L.append(rf"\draw[thin] (0,0) -- (0:{S*R3+0.3:.3f}); \draw[thin] (0,0) -- (30:{S*R3+0.3:.3f});")
L.append(rf"\draw[inkmuted] (0:{S:.3f}) arc (0:40:{S:.3f}); \draw[inkmuted] (0:{S*R3:.3f}) arc (0:40:{S*R3:.3f});")
L.append(rf"\draw[thick, copper] (0:{S:.3f}) -- (30:{S*R3:.3f});")
L.append(rf"\fill (0,0) circle (1.6pt) node[left, font=\small] {{$P$}};")
L.append(rf"\fill (0:{S:.3f}) circle (1.6pt); \fill (30:{S*R3:.3f}) circle (1.6pt);")
L.append(rf"\node[font=\small] at (16:{S*1.62:.3f}) {{$1$}};")
L.append(rf"\draw (0:0.55) arc (0:30:0.55); \node[font=\scriptsize] at (15:0.8) {{$30^\circ$}};")
L.append(rf"\node[below, font=\small] at (0:{S*0.5:.3f}) {{$1$}}; \node[font=\small] at (38:{S*1.2:.3f}) {{$\sqrt3$}};")
L.append(rf"\node[font=\small] at ({S*0.9:.3f},-0.75) {{(a)}};")
L.append(r"\end{scope}")
# panel (b), shifted right
dx = 5.4
L.append(rf"\begin{{scope}}[shift={{({dx},0)}}]")
L.append(rf"\fill[copper!12] (0:{S:.3f}) arc (0:180:{S:.3f}) -- (180:{S*R3:.3f}) arc (180:0:{S*R3:.3f}) -- cycle;")
L.append(rf"\draw[inkmuted] (0:{S:.3f}) arc (0:180:{S:.3f}); \draw[inkmuted] (0:{S*R3:.3f}) arc (0:180:{S*R3:.3f});")
L.append(rf"\draw[thin] (-{S*R3+0.3:.3f},0) -- ({S*R3+0.3:.3f},0);")
pts = []
for k in range(6):
    a = 35 * k + 2
    r = 1.73 if k % 2 == 0 else 1.25
    pts.append((r * math.cos(math.radians(a)), r * math.sin(math.radians(a))))
assert all(math.dist(p, q) > 1 for p, q in combinations(pts, 2)) and all(1 < math.hypot(*p) <= R3 for p in pts)
for p in pts:
    L.append(rf"\draw[thin] (0,0) -- ({S*p[0]:.3f},{S*p[1]:.3f}); \fill ({S*p[0]:.3f},{S*p[1]:.3f}) circle (1.6pt);")
L.append(rf"\fill (0,0) circle (1.8pt) node[below, font=\small] {{$P$}};")
L.append(rf"\node[font=\small] at (0,-0.75) {{(b)}};")
L.append(r"\end{scope}")
HERE = Path(__file__).resolve().parent
out = ((HERE.parent / "paper" / "figs") if (HERE.parent / "paper").exists() else (HERE.parent / "note" / "figs")) / "sevenproof.tex"
out.write_text("\n".join(L) + "\n")
print("wrote", out, "min pairwise", min(math.dist(p, q) for p, q in combinations(pts, 2)))
