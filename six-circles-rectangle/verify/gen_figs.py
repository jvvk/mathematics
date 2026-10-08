"""TikZ figures for the note, drawn from coords.json (written by check_note.py). Never edit fig_*.tex by hand."""
import json
import os
HERE = os.path.dirname(os.path.abspath(__file__))
D = json.load(open(os.path.join(HERE, "coords.json"))); p = D["pts"]; r = D["r"]; w = D["w"]
f = lambda k: f"({p[k][0]:.4f},{p[k][1]:.4f})"
def circles(style="black!70"):
    out = []
    for k, rad in (("A", r["a"]), ("B", r["b"]), ("C", r["c"]), ("Ap", r["a"]), ("Bp", r["b"]), ("Cp", r["c"])):
        out.append(f"\\draw[{style}] {f(k)} circle ({rad:.4f});")
    return "\n".join(out)
rect = f"\\draw[thick] ({-w:.4f},-1) rectangle ({w:.4f},1);"
dot = lambda k, lab, pos: f"\\fill {f(k)} circle (0.9pt) node[{pos}, font=\\small] {{{lab}}};"

omega = "\\draw[densely dashed, gray] (0,0) circle (1);"

def fig_config():
    return "\n".join([r"\begin{tikzpicture}[scale=2.6]", rect, circles(), omega,
        f"\\draw[red, very thick] {f('A')} -- {f('Ap')};",
        f"\\draw[densely dashed, blue!70!black] {f('O')} -- {f('B')};",
        dot("O", "$O$", "below left"), dot("A", "$A$", "above left"), dot("B", "$B$", "above"),
        dot("C", "$C$", "above right"), dot("Ap", "$A'$", "below right"), dot("Bp", "$B'$", "below"),
        dot("Cp", "$C'$", "below left"), r"\end{tikzpicture}"])

def fig_bisector():
    return "\n".join([r"\begin{tikzpicture}[scale=2.6]", rect, circles("black!35"),
        f"\\draw[green!50!black, thick] {f('O')} -- {f('U')};",
        f"\\draw[green!50!black, thick] {f('O')} -- {f('Bt')};",
        f"\\draw[orange!90!black, thick] {f('O')} -- {f('M')};",
        f"\\draw[orange!90!black, thick] {f('At')} -- {f('Cb')};",
        f"\\draw[blue!70!black, thick] {f('A')} -- {f('Cp')};",
        dot("O", "$O$", "below right"), dot("U", "$U$", "above left"), dot("M", "$M$", "above"),
        dot("Bt", "$B_t$", "above right"), dot("At", "$A_t$", "above=2pt"), dot("Ct", "$C_t$", "above"),
        dot("T", "$T$", "right"), dot("Cb", "$C'_b$", "below"), dot("A", "$A$", "left"), dot("Cp", "$C'$", "left"),
        r"\end{tikzpicture}"])

def fig_triangles():
    iso = f"\\filldraw[fill=blue!10, draw=blue!70!black, thick] {f('O')} -- {f('E')} -- {f('A')} -- cycle;"
    left = "\n".join([r"\begin{tikzpicture}[scale=2.2]", rect, circles("black!20"), omega, iso,
        f"\\draw[green!50!black] {f('O')} -- {f('U')} {f('O')} -- {f('Bt')};",
        f"\\draw[densely dashed] ({-w:.4f},0) -- ({w:.4f},0);",
        f"\\draw[blue!70!black] {f('A')} -- {f('Cp')};",
        dot("O", "$O$", "below right"), dot("U", "$U$", "above left"), dot("Bt", "$B_t$", "above right"),
        dot("K", "$K$", "right"), dot("E", "$E'$", "below left"), dot("A", "$A$", "above left"),
        r"\end{tikzpicture}"])
    # magnified panel: both small right triangles at the same scale, each in its own orientation
    F = 22.0
    def tri(keys, shift, labels, right_at, psi_at):
        (x0, y0) = p[keys[0]]
        pt = {k: ((p[k][0] - x0) * F + shift[0], (p[k][1] - y0) * F + shift[1]) for k in keys}
        g = lambda k: f"({pt[k][0]:.3f},{pt[k][1]:.3f})"
        out = [f"\\filldraw[fill=orange!20, draw=orange!90!black, thick] {g(keys[0])} -- {g(keys[1])} -- {g(keys[2])} -- cycle;",
               f"\\draw[orange!90!black, very thick] {g(keys[0])} -- {g(keys[1])} node[midway, sloped, below, font=\\scriptsize] {{$UM$}};",
               f"\\node[font=\\scriptsize] at ($({g(psi_at)})!0.28!({g(keys[2])})$) {{}};",
               None]
        # draw the angle at psi_at between its two other vertices, anticlockwise from the first ray (the small angle)
        o_ = [k for k in keys if k != psi_at]
        v1 = (pt[o_[0]][0]-pt[psi_at][0], pt[o_[0]][1]-pt[psi_at][1]); v2 = (pt[o_[1]][0]-pt[psi_at][0], pt[o_[1]][1]-pt[psi_at][1])
        first, second = (o_[0], o_[1]) if v1[0]*v2[1]-v1[1]*v2[0] > 0 else (o_[1], o_[0])
        out[3] = f"\\draw pic[draw, angle radius=10mm, \"$\\psi$\", angle eccentricity=1.25, font=\\scriptsize] {{angle={first}--{psi_at}--{second}}};"
        names = "\n".join(f"\\coordinate ({k}) at {g(k)};" for k in keys)
        labs = "\n".join(f"\\node[{pos}, font=\\small] at {g(k)} {{{lab}}};" for k, (lab, pos) in labels.items())
        return names + "\n" + "\n".join(out[:2] + out[3:]) + "\n" + labs
    t1 = tri(["M", "K", "Bt"], (0.0, 0.0), {"M": ("$M$", "above left"), "K": ("$K$", "below right"), "Bt": ("$B_t$", "above right")}, "K", "M")
    t2 = tri(["S", "S0", "E"], (3.4, -0.2), {"S": ("$S$", "below left"), "S0": ("$S_0$", "above left"), "E": ("$E'$", "above right")}, "S0", "S")
    right = "\n".join([r"\begin{tikzpicture}", t1, t2, r"\end{tikzpicture}"])
    return left + "\n\\qquad\n" + right

for name, fn in (("fig_config", fig_config), ("fig_bisector", fig_bisector), ("fig_triangles", fig_triangles)):
    open(os.path.join(HERE, "..", "paper", name + ".tex"), "w").write(fn() + "\n")
print("wrote 3 figures")
