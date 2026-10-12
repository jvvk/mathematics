"""Writes note/figs/arcs.tex: left, the semicircles z = 1 - r e^{iu} (r = 3, 5, 7, 9) and the trivial zeros;
right, log|zeta(z(u))| against u for the same radii (mpmath, plotting only)."""
from pathlib import Path

import mpmath as mp

mp.mp.dps = 20
OUT = Path(__file__).resolve().parent.parent / "paper" / "figs" / "arcs.tex"
COL = {3: "blue!60!black", 5: "copper", 7: "inkmuted", 9: "black!35"}


def main():
    out = ["\\begin{tikzpicture}[font=\\small]", "\\begin{scope}[scale=0.28]"]
    out.append("\\draw[inkmuted,->] (-9.5,0) -- (11,0) node[right] {$\\operatorname{Re} z$};")
    out.append("\\draw[inkmuted,->] (0,-10) -- (0,1.5);")
    for r in (3, 5, 7, 9):
        pts = " ".join(f"({float(1 - r * mp.cos(mp.pi * k / 60)):.3f},{float(-r * mp.sin(mp.pi * k / 60)):.3f})"
                       for k in range(61))
        w = "thick" if r == 5 else "semithick"
        out.append(f"\\draw[{COL[r]},{w}] plot coordinates {{{pts}}};")
        out.append(f"\\node[{COL[r]},below,font=\\scriptsize] at ({1 - r},-{0.2 if r > 3 else 0.2}) {{}};")
    for k in (2, 4, 6, 8):
        out.append(f"\\fill (-{k},0) circle (5pt) node[above,font=\\scriptsize] {{$-{k}$}};")
    out.append("\\fill (1,0) circle (3pt);")
    out.append("\\end{scope}")
    out.append("\\begin{scope}[xshift=7.2cm,yshift=0.3cm,x=1.25cm,y=0.36cm]")
    out.append("\\draw[inkmuted,->] (0,0) -- (3.4,0) node[right] {$u$};")
    out.append("\\node[left,inkmuted,font=\\scriptsize] at (0,0) {$0$};")
    out.append("\\node[left,inkmuted,font=\\scriptsize] at (0,-7) {$-7$};")
    out.append("\\draw[inkmuted,->] (0,-7.5) -- (0,1.8) node[above] {$\\log|\\zeta(z(u))|$};")
    out.append("\\node[below,inkmuted] at (3.1416,0) {$\\pi$};")
    out.append("\\draw[inkmuted] (3.1416,-0.1) -- (3.1416,0.1);")
    for r in (3, 5, 7, 9):
        pts = []
        for k in range(1, 121):
            u = mp.pi * k / 120
            z = 1 - r * mp.e ** (1j * u)
            v = float(mp.log(abs(mp.zeta(z))))
            if v > -7:
                pts.append(f"({float(u):.3f},{v:.3f})")
        w = "thick" if r == 5 else "semithick"
        out.append(f"\\draw[{COL[r]},{w}] plot[smooth] coordinates {{{' '.join(pts)}}};")
    out.append("\\end{scope}")
    out.append("\\end{tikzpicture}")
    OUT.parent.mkdir(parents=True, exist_ok=True)
    OUT.write_text("\n".join(out) + "\n")
    print("wrote", OUT)


if __name__ == "__main__":
    main()
