"""Write figs/taxi11.tex and book/figs/taxi11table.tex for the n = 11 placement, translated into the box
[0,23] x [0,49] and lettered A..K in lexicographic order. The figure labels every point with its coordinates and marks
the distance-1 and distance-55 pairs; the table gives the 55 distances as a triangular matrix and, for lookup, the pair
realising each distance 1..55. Asserts that the distances are exactly 1..55 before writing anything."""

from itertools import combinations
from pathlib import Path

RAW = [
    (-8, 25),
    (-22, -4),
    (-5, 29),
    (-14, -13),
    (1, 6),
    (-15, -9),
    (1, -20),
    (-21, -4),
    (-11, -18),
    (-22, -6),
    (-10, -13),
]
x0, y0 = min(x for x, _ in RAW), min(y for _, y in RAW)
Q = sorted((x - x0, y - y0) for x, y in RAW)
NAME = "ABCDEFGHIJK"
dist = lambda p, q: abs(p[0] - q[0]) + abs(p[1] - q[1])
pair_of = {dist(Q[i], Q[j]): NAME[i] + NAME[j] for i, j in combinations(range(11), 2)}
assert sorted(pair_of) == list(range(1, 56)) and len(pair_of) == 55
W, H = max(x for x, _ in Q), max(y for _, y in Q)
S = 0.16
POS = dict(
    A="left",
    B="above left",
    C="above right",
    D="left",
    E="left",
    F="below",
    G="right",
    H="left",
    I="left",
    J="right",
    K="right",
)

far = max(combinations(Q, 2), key=lambda pq: dist(*pq))
near = min(combinations(Q, 2), key=lambda pq: dist(*pq))
fig = [
    f"\\draw[line width=0.15pt, inkmuted!35, step={S}] (0,0) grid ({W * S:.3f},{H * S:.3f});",
    f"\\draw[copper, thick] ({far[0][0] * S:.3f},{far[0][1] * S:.3f}) -- ({far[1][0] * S:.3f},{far[0][1] * S:.3f}) -- ({far[1][0] * S:.3f},{far[1][1] * S:.3f});",
]
dots = []  # drawn after the labels, so the white label backgrounds never cover a dot
for k, (x, y) in enumerate(Q):
    dots.append(
        f"\\fill[{'copper' if (x + y) % 2 else 'black'}] ({x * S:.3f},{y * S:.3f}) circle (2.2pt);"
    )
    fig.append(
        f"\\node[{POS[NAME[k]]}, font=\\scriptsize, inner sep=1.2pt, fill=white, fill opacity=0.85, text opacity=1, outer sep=2.8pt] at ({x * S:.3f},{y * S:.3f}) {{$\\mathrm{{{NAME[k]}}}\\,({x},{y})$}};"
    )
fig += dots
fig.append(
    f"\\draw ({(near[0][0] + near[1][0]) / 2 * S:.3f},{near[0][1] * S:.3f}) ellipse (6pt and 4pt);"
)
for v in (0, W):
    fig.append(f"\\node[below, font=\\tiny, inkmuted] at ({v * S:.3f},-0.05) {{{v}}};")
for v in (0, H):
    fig.append(f"\\node[left, font=\\tiny, inkmuted] at (-0.05,{v * S:.3f}) {{{v}}};")

tab = ["\\begin{tabular}{@{}c|" + "r" * 10 + "@{}}"]
tab.append(" & " + " & ".join(f"$\\mathrm{{{c}}}$" for c in NAME[:10]) + "\\\\\\hline")
for i in range(1, 11):
    cells = [str(dist(Q[i], Q[j])) for j in range(i)] + [""] * (10 - i)
    tab.append(f"$\\mathrm{{{NAME[i]}}}$ & " + " & ".join(cells) + "\\\\")
tab.append("\\end{tabular}\\\\[1.2em]")
tab.append("\\begin{tabular}{@{}" + "rl" * 5 + "@{}}")
for r in range(11):
    tab.append(" & ".join(f"{d} & {pair_of[d]}" for d in range(r + 1, 56, 11)) + "\\\\")
tab.append("\\end{tabular}")

HERE = Path(__file__).resolve().parent
figs = (HERE.parent / "paper" / "figs") if (HERE.parent / "paper").exists() else (HERE.parent / "note" / "figs")
(figs / "taxi11.tex").write_text("\n".join(fig) + "\n")
(figs / "taxi11table.tex").write_text("\n".join(tab) + "\n")
print("points", dict(zip(NAME, Q)), "box", W, H, "near", near, "far", far)
