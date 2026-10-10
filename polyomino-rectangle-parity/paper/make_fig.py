"""Generate fig_pieces.tex: the T-tetromino and the three octominoes with the largest checkerboard imbalance (4),
cells coloured by (x + y) mod 2. verify/check.py (claim P2) asserts that these three are exactly the octominoes
with imbalance 4, and that no octomino has a larger one.

    ~/.venvs/main/bin/python make_fig.py
"""

from pathlib import Path

PIECES = [
    ("T-tetromino, $c=2$", [(0, 0), (0, 1), (0, 2), (1, 1)]),
    ("$c=4$", [(0, 0), (0, 1), (0, 2), (1, 1), (2, 0), (2, 1), (2, 2), (3, 1)]),
    ("$c=4$", [(0, 1), (0, 3), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (2, 1)]),
    ("$c=4$", [(0, 1), (1, 0), (1, 1), (1, 2), (2, 1), (2, 2), (2, 3), (3, 2)]),
]

out = ["\\begin{tikzpicture}[x=0.42cm,y=0.42cm]"]
x0 = 0
for label, cells in PIECES:
    w = max(x for x, _ in cells) + 1
    for x, y in cells:
        fill = "inkblue" if (x + y) % 2 == 0 else "softblue"
        out.append(f"  \\fill[{fill},draw=inkblue,thick] ({x0 + x},{y}) rectangle ++(1,1);")
    out.append(f"  \\node[below,font=\\small] at ({x0 + w / 2},-0.2) {{{label}}};")
    x0 += w + 2.5
out.append("\\end{tikzpicture}")
Path(__file__).with_name("fig_pieces.tex").write_text("\n".join(out) + "\n")
print("wrote fig_pieces.tex")
