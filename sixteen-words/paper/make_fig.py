"""Write fig_cover.tex: the 16 words as rows of cells (dark = 1), grouped into orbits under complement and
reversal, and one 15-bit string with the five deleted bits struck out, leaving one of the words.

    python3 make_fig.py
"""
from __future__ import annotations

S16 = ("0000000000 0000000011 0000111110 0011001100 0011111111 0110000110 0110101001 0111110000 "
       "1000001111 1001010110 1001111001 1100000000 1100110011 1111000001 1111111100 1111111111").split()
EXAMPLE = "101100111010010"


def orbit(w: str) -> frozenset[str]:
    c = w.translate(str.maketrans("01", "10"))
    return frozenset({w, c, w[::-1], c[::-1]})


def embed(y: str, x: str) -> list[int] | None:
    pos, j = [], 0
    for i, ch in enumerate(x):
        if j < len(y) and ch == y[j]:
            pos.append(i)
            j += 1
    return pos if j == len(y) else None


orbs: list[frozenset[str]] = []
for w in S16:
    if orbit(w) not in orbs:
        orbs.append(orbit(w))
rows = [w for o in orbs for w in sorted(o)]
assert sorted(rows) == sorted(S16)
hit = next(w for w in rows if embed(w, EXAMPLE))
keep = embed(hit, EXAMPLE)

c = 0.32
out = ["\\begin{tikzpicture}[x=1cm,y=1cm]"]
y = 0.0
for k, o in enumerate(orbs):
    for w in sorted(o):
        for i, b in enumerate(w):
            fill = "inkblue" if b == "1" else "white"
            out.append(f"  \\filldraw[fill={fill},draw=gray!50] ({i * c:.2f},{-y:.2f}) rectangle ++({c},{-c});")
        if w == hit:
            out.append(f"  \\draw[rust,very thick] ({-0.05:.2f},{-y + 0.05:.2f}) rectangle ({10 * c + 0.05:.2f},{-y - c - 0.05:.2f});")
        y += c
    y += 0.12
out.append(f"  \\node[font=\\scriptsize,anchor=south] at ({5 * c:.2f},0.05) {{16 words of length 10}};")
x0 = 10 * c + 1.2
ty = -2.0
out.append(f"  \\node[font=\\scriptsize,anchor=south] at ({x0 + 7.5 * c:.2f},{ty + 0.05:.2f}) {{a string of length 15}};")
for i, b in enumerate(EXAMPLE):
    fill = "inkblue" if b == "1" else "white"
    out.append(f"  \\filldraw[fill={fill},draw=gray!50] ({x0 + i * c:.2f},{ty:.2f}) rectangle ++({c},{-c});")
    if i not in keep:
        out.append(f"  \\draw[rust,thick] ({x0 + i * c:.2f},{ty:.2f}) -- ++({c},{-c}) ({x0 + i * c:.2f},{ty - c:.2f}) -- ++({c},{c});")
ty2 = ty - 1.0
out.append(f"  \\node[font=\\scriptsize,anchor=south] at ({x0 + 7.5 * c:.2f},{ty2 + 0.05:.2f}) {{delete five bits}};")
for j, i in enumerate(keep):
    b = EXAMPLE[i]
    fill = "inkblue" if b == "1" else "white"
    out.append(f"  \\filldraw[fill={fill},draw=gray!50] ({x0 + (2.5 + j) * c:.2f},{ty2:.2f}) rectangle ++({c},{-c});")
out.append(f"  \\draw[rust,very thick] ({x0 + 2.5 * c - 0.05:.2f},{ty2 + 0.05:.2f}) rectangle ({x0 + 12.5 * c + 0.05:.2f},{ty2 - c - 0.05:.2f});")
out.append("\\end{tikzpicture}")
open("fig_cover.tex", "w").write("\n".join(out) + "\n")
print("orbits:", [len(o) for o in orbs], "| example covered by", hit, "keeping positions", keep)
