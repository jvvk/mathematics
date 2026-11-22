"""Generate figs/pattern.tex (a p = 0.3 pattern, loops shaded) and figs/density.tex (graph of c(p))."""
import random
from math import pi, sin, tan

def closed(p):
    q = 1 - p; r = p * q
    return 2*r - 1.25 + pi**2*r**2/6*(2 + 3/sin(pi*p)**2) + pi*r*(1 - 3*r)/tan(pi*p)/(1 - 2*p)

rng = random.Random(11)
n, m, p = 18, 12, 0.3
eps = [0 if rng.random() < p else 1 for _ in range(n + 1)]
eta = [0 if rng.random() < p else 1 for _ in range(m + 1)]
adj = {}
segs = []
def add(a, b):
    adj.setdefault(a, []).append(b); adj.setdefault(b, []).append(a); segs.append((a, b))
for i in range(n + 1):
    for j in range(m):
        if j % 2 == eps[i]: add((i, j), (i, j + 1))
for j in range(m + 1):
    for i in range(n):
        if i % 2 == eta[j]: add((i, j), (i + 1, j))
seen, cycles = set(), []
for s in adj:
    if s in seen: continue
    cyc, prev, cur, ok = [s], None, s, True
    while True:
        if len(adj[cur]) != 2: ok = False; break
        nxt = adj[cur][0] if prev is None else next(v for v in adj[cur] if v != prev)
        prev, cur = cur, nxt
        if cur == s: break
        cyc.append(cur)
    seen.update(cyc)
    if ok: cycles.append(cyc)
out = [r"\begin{tikzpicture}[scale=0.42]"]
for c in cycles:
    out.append(r"\fill[loopfill] " + " -- ".join(f"({x},{y})" for x, y in c) + " -- cycle;")
out.append(rf"\draw[gridline] (0,0) grid ({n},{m});")
for (a, b) in segs:
    out.append(rf"\draw[stitch] ({a[0]},{a[1]}) -- ({b[0]},{b[1]});")
for i, e in enumerate(eps):
    out.append(rf"\node[lab] at ({i},-0.6) {{{e}}};")
for j, e in enumerate(eta):
    out.append(rf"\node[lab] at (-0.6,{j}) {{{e}}};")
out.append(r"\end{tikzpicture}")
open("pattern.tex", "w").write("\n".join(out) + "\n")
print("loops in figure:", len(cycles), "labels", eps, eta)

pts = " ".join(f"({k/200:.3f},{closed(k/200):.6f})" for k in range(2, 199) if k != 100)
pts = pts.replace("(0.495", "(0.495").replace(" (0.505", f" (0.500,{(pi**2-9)/12:.6f}) (0.505")
open("density.tex", "w").write(r"""\begin{tikzpicture}
\begin{axis}[width=0.72\textwidth,height=0.42\textwidth,xmin=0,xmax=1,ymin=0,ymax=0.26,
  xlabel={$p$},ylabel={$c(p)$},xtick={0,0.25,0.5,0.75,1},ytick={0,0.05,0.1,0.15,0.2,0.25},
  tick label style={font=\footnotesize},yticklabel style={/pgf/number format/fixed,/pgf/number format/precision=2},label style={font=\small}]
\addplot[thick,smooth] coordinates {""" + pts + r"""};
\addplot[only marks,mark=*,mark size=1.6pt] coordinates {(0.5,""" + f"{(pi**2-9)/12:.6f}" + r""")};
\node[anchor=south,font=\footnotesize] at (axis cs:0.5,0.082) {$\frac{\pi^2-9}{12}$};
\addplot[dashed] coordinates {(0,0.25) (1,0.25)};
\end{axis}
\end{tikzpicture}
""")
