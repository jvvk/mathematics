"""Writes fig_family.tex: the 6a+1 family with a = 3, and one path from 4 to m1 that passes the new vertex m2.

H has edges 01, 12, 13, 14, 23, 24; the new vertices m1, m2, m3 are joined to x = 0 and y = 3.
Run: python3 make_fig.py > fig_family.tex
"""
POS = {"0": (0.0, 0.0), "1": (1.8, 0.0), "2": (3.6, 0.0), "4": (2.7, -1.5), "3": (2.7, 1.6),
       "m1": (0.2, 2.4), "m2": (0.9, 3.0), "m3": (1.6, 3.6)}
LABEL = {"m1": "$m_1$", "m2": "$m_2$", "m3": "$m_3$"}
H = [("0", "1"), ("1", "2"), ("1", "3"), ("1", "4"), ("2", "3"), ("2", "4")]
NEW = [(m, e) for m in ("m1", "m2", "m3") for e in ("0", "3")]
PATH = ["4", "2", "3", "m2", "0", "m1"]


def main() -> str:
    on_path = {frozenset(p) for p in zip(PATH, PATH[1:])}
    out = [r"\begin{tikzpicture}[scale=1.05, every node/.style={font=\small},",
           r"  v/.style={circle, draw=inkblue, fill=softblue, inner sep=1.6pt, minimum size=17pt},",
           r"  n/.style={circle, draw=rust, fill=white, inner sep=1.2pt, minimum size=17pt}]"]
    for e in H + NEW:
        style = "rust, line width=1.6pt" if frozenset(e) in on_path else ("inkblue!70" if e in H else "rust!55")
        (x0, y0), (x1, y1) = POS[e[0]], POS[e[1]]
        out.append(rf"\draw[{style}] ({x0},{y0}) -- ({x1},{y1});")
    for name, (x, y) in POS.items():
        st = "n" if name.startswith("m") else "v"
        out.append(rf"\node[{st}] ({name}) at ({x},{y}) {{{LABEL.get(name, name)}}};")
    out.append(r"\node[font=\small, text=black!60, anchor=west] at (3.1,1.6) {$y$};")
    out.append(r"\node[font=\small, text=black!60, anchor=east] at (-0.35,0) {$x$};")
    out.append(r"\end{tikzpicture}")
    return "\n".join(out)


if __name__ == "__main__":
    print(main())
