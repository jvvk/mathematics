"""Write fig_poles.tex: the poles of P_9(q) on the unit circle, one ring per family m (primitive 2m-th roots,
floor(9/m) odd), drawn solid when rho' = min(9 mod m, m - 1 - 9 mod m) >= 1 (the family can bring a new conductor)
and hollow when rho' = 0. Asserts the family list against residues.poles."""
import math
import pathlib
import sys

sys.path.insert(0, str(pathlib.Path(__file__).resolve().parent.parent / "verify"))
from residues import poles  # noqa: E402

N = 9
fams = sorted({m for m, _ in poles(N)})
assert fams == [1, 3, 5, 6, 7, 8, 9], fams
out = ["\\begin{tikzpicture}[scale=1.75]"]
out.append("  \\draw[gray!50] (0,0) circle (1);")
out.append("  \\draw[gray!35,->] (-1.25,0) -- (1.3,0); \\draw[gray!35,->] (0,-1.2) -- (0,1.25);")
legend = []
for idx, m in enumerate(fams):
    rho = N % m
    rp = min(rho, m - 1 - rho)
    r = 1 + 0.07 * idx if m > 1 else 1
    live = rp >= 1
    col = "rust" if live else "inkblue"
    for mm, j in poles(N):
        if mm != m:
            continue
        a = math.pi * j / m
        x, y = r * math.cos(a), r * math.sin(a)
        style = f"fill={col}, draw={col}" if live else f"fill=white, draw={col}, thick"
        out.append(f"  \\draw[{style}] ({x:.4f},{y:.4f}) circle (0.028);")
    legend.append((m, rho, rp, col, live))
y0 = 1.05
out.append(f"  \\node[right,font=\\small] at (1.55,{y0 + 0.18:.2f}) {{$m$: $\\rho$, $\\rho'$}};")
for i, (m, rho, rp, col, live) in enumerate(legend):
    yy = y0 - 0.25 * i
    style = f"fill={col}, draw={col}" if live else f"fill=white, draw={col}, thick"
    out.append(f"  \\draw[{style}] (1.62,{yy:.2f}) circle (0.028);")
    out.append(f"  \\node[right,font=\\small] at (1.7,{yy:.2f}) {{${m}$: ${rho}$, ${rp}$}};")
out.append("\\end{tikzpicture}")
pathlib.Path(__file__).with_name("fig_poles.tex").write_text("\n".join(out) + "\n")
