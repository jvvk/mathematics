"""Writes the note's TikZ figures from noncongruent_9.json (so the pictures are the data)."""
from __future__ import annotations

import json

sols = json.load(open("noncongruent_9.json"))
SHADES = ["blue!12", "orange!18", "green!14", "red!12", "violet!14", "yellow!25", "cyan!14", "brown!16", "gray!16"]


def tikz(sol, size_cm: float, labels: bool) -> str:
    side, R = sol["side"], sol["rects"]
    u = size_cm / side
    out = [f"\\begin{{tikzpicture}}[x={u:.5f}cm,y={u:.5f}cm]"]
    for k, (a, b, c, d) in enumerate(sorted(R, key=lambda r: ((r[1] - r[0]) * (r[3] - r[2])))):
        out.append(f"\\filldraw[fill={SHADES[k]},draw=black,line width=0.4pt] ({a},{c}) rectangle ({b},{d});")
        if labels:
            w, h = b - a, d - c
            fs = "\\scriptsize" if min(w, h) >= 9 else "\\tiny"
            text = f"${w}\\times{h}$"
            rot = ",rotate=90" if h > 2.5 * w else ""
            if min(w, h) >= 5:
                out.append(f"\\node[font={fs}{rot}] at ({(a + b) / 2},{(c + d) / 2}) {{{text}}};")
            else:  # thin strip: label outside with a leader
                out.append(f"\\node[font=\\tiny{rot}] at ({(a + b) / 2},{(c + d) / 2}) {{}};")
    out.append(f"\\draw[line width=0.9pt] (0,0) rectangle ({side},{side});")
    out.append("\\end{tikzpicture}")
    return "\n".join(out)


open("../paper/fig_square84.tex", "w").write(tikz(sols[1], 7.0, True) + "\n")
parts = []
for s in sols:
    parts.append("\\begin{minipage}[b]{0.19\\textwidth}\\centering\n" + tikz(s, 2.6, False)
                 + f"\\\\[2pt]{{\\footnotesize side {s['side']}, perimeter {s['perimeter']}}}\n\\end{{minipage}}")
open("../paper/fig_all5.tex", "w").write("\\hfill\n".join(parts) + "\n")

# Mechanism figure: three pieces, unknown cut positions x, y, semi-perimeter s
mech = r"""\begin{tikzpicture}[scale=3]
\filldraw[fill=blue!12] (0,0) rectangle (0.25,1);
\filldraw[fill=orange!18] (0.25,0) rectangle (1,0.5);
\filldraw[fill=green!14] (0.25,0.5) rectangle (1,1);
\draw[line width=0.9pt] (0,0) rectangle (1,1);
\node[font=\small] at (0.125,0.5) {$P_1$};
\node[font=\small] at (0.625,0.25) {$P_3$};
\node[font=\small] at (0.625,0.75) {$P_2$};
\draw[|<->|,thin] (0,-0.08) -- node[below,font=\small] {$x$} (0.25,-0.08);
\draw[|<->|,thin] (1.08,0) -- node[right,font=\small] {$y$} (1.08,0.5);
\draw[|<->|,thin] (0,1.08) -- node[above,font=\small] {$1$} (1,1.08);
\end{tikzpicture}"""
open("../paper/fig_mechanism.tex", "w").write(mech + "\n")
print("figures written")

# Introduction list (side-84 solution, in the figure's orientation, sorted by area) and Table 1 rows
s84 = sols[1]
pcs = sorted(s84["rects"], key=lambda r: (r[1] - r[0]) * (r[3] - r[2]))
dims = ",\\quad ".join(f"{b - a}\\times{d - c}" for a, b, c, d in pcs)
areas = ", ".join(str((b - a) * (d - c)) for a, b, c, d in pcs)
open("../paper/intro_list.tex", "w").write(f"\\[\n{dims}\n\\]\nwith areas ${areas}$%")
rows = []
for s in sols:
    R = sorted(s["rects"])
    cells = ", ".join(f"$[{a},{b}]\\times[{c},{d}]$" for a, b, c, d in R)
    rows.append(f"{s['side']} & {s['perimeter']} & \\parbox[t]{{0.74\\textwidth}}{{\\raggedright {cells}}}\\\\[3pt]")
open("../paper/table_all5.tex", "w").write(
    "\\begin{tabular}{@{}rrl@{}}\n\\toprule\nside & perimeter & pieces, as $[x_1,x_2]\\times[y_1,y_2]$ \\\\\n\\midrule\n"
    + "\n".join(rows) + "\n\\bottomrule\n\\end{tabular}\n")
print("list and table written")
