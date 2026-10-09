"""TikZ figures from the d = 3 certificates: a cube net P and -P + t tiling the plane.
Cells of P are blue, cells of -P + t red; thick lines separate tiles."""
from __future__ import annotations
import itertools, re, sys
sys.path.insert(0, "../verify")
from verify2 import Group, parse_cells

def tiling(uid: int, W: int, H: int) -> dict[tuple[int, int], tuple[int, int]]:
    cells = parse_cells("../verify/certificates/cert_d3.txt")
    line = next(l for l in open("../verify/certificates/inv_d3.txt") if int(l.split()[0]) == uid)
    G = Group([int(x) for x in re.search(r"group=([\dx]+)", line).group(1).split("x")])
    imgs = [tuple(map(int, c.split(","))) for c in re.findall(r"\(([\d,]+)\)", re.search(r"phi=(\S+)", line).group(1))]
    phi = lambda v: tuple(sum(v[j] * imgs[j][i] for j in range(2)) % G.f[i] for i in range(len(G.f)))
    P = cells[uid]; Q = [(-x, -y) for x, y in P]
    A = {phi(p) for p in P}
    t = next(v for v in sorted(itertools.product(range(-6, 7), repeat=2), key=lambda v: max(map(abs, v)))
             if not A & {phi((q[0] + v[0], q[1] + v[1])) for q in Q})
    Q = [(q[0] + t[0], q[1] + t[1]) for q in Q]
    lab: dict[tuple[int, int], tuple[int, int]] = {}
    for lx, ly in itertools.product(range(-12, W + 12), range(-12, H + 12)):
        if phi((lx, ly)) != G.zero():
            continue
        for k, tile in enumerate((P, Q)):
            for c in tile:
                x, y = c[0] + lx, c[1] + ly
                if 0 <= x < W and 0 <= y < H:
                    assert (x, y) not in lab, "overlap"
                    lab[(x, y)] = (k, lx * 1000 + ly)
    assert len(lab) == W * H, "gap"
    return lab

def tikz(lab, W: int, H: int, s: float = 0.42) -> str:
    out = [f"\\begin{{tikzpicture}}[x={s}cm,y={s}cm]"]
    for (x, y), (k, _) in lab.items():
        col = "tileA" if k == 0 else "tileB"
        out.append(f"\\fill[{col}] ({x},{y}) rectangle ({x+1},{y+1});")
    out.append(f"\\draw[white!70!black,line width=0.2pt] (0,0) grid ({W},{H});")
    for (x, y), v in lab.items():  # tile boundaries
        if x + 1 < W and lab[(x + 1, y)] != v: out.append(f"\\draw[thick] ({x+1},{y}) -- ({x+1},{y+1});")
        if y + 1 < H and lab[(x, y + 1)] != v: out.append(f"\\draw[thick] ({x},{y+1}) -- ({x+1},{y+1});")
    out.append(f"\\draw[thick] (0,0) rectangle ({W},{H});")
    out.append("\\end{tikzpicture}")
    return "\n".join(out)

def net(uid: int, s: float = 0.42) -> str:
    P = parse_cells("../verify/certificates/cert_d3.txt")[uid]
    out = [f"\\begin{{tikzpicture}}[x={s}cm,y={s}cm]"]
    for x, y in P: out.append(f"\\fill[tileA] ({x},{y}) rectangle ({x+1},{y+1}); \\draw[thick] ({x},{y}) rectangle ({x+1},{y+1});")
    out.append("\\end{tikzpicture}")
    return "\n".join(out)

def mechanism(uid: int, s: float = 0.55) -> str:
    """P labelled by phi, -P + t labelled by phi, and the group Z_12 split into A and s - A."""
    cells = parse_cells("../verify/certificates/cert_d3.txt")
    line = next(l for l in open("../verify/certificates/inv_d3.txt") if int(l.split()[0]) == uid)
    assert "group=12 " in line
    a, b = (int(c) for c in re.findall(r"\((\d+)\)", re.search(r"phi=(\S+)", line).group(1)))
    phi = lambda v: (a * v[0] + b * v[1]) % 12
    P = cells[uid]
    A = {phi(p) for p in P}
    assert len(A) == 6
    sums = {(x + y) % 12 for x in A for y in A}
    sv = min(set(range(12)) - sums)
    t = next(v for v in sorted(itertools.product(range(-6, 7), repeat=2), key=lambda v: (max(map(abs, v)), v))
             if phi(v) == sv)
    Q = [(t[0] - x, t[1] - y) for x, y in P]
    assert {phi(q) for q in Q} == set(range(12)) - A
    minx = min(x for x, _ in P); miny = min(y for _, y in P)
    P = [(x - minx, y - miny) for x, y in P]
    shift = max(x for x, _ in P) + 3
    qx = min(x for x, _ in Q); qy = min(y for _, y in Q)
    out = [f"\\begin{{tikzpicture}}[x={s}cm,y={s}cm]"]
    for (x, y), (x0, y0) in zip(P, cells[uid]):
        out.append(f"\\fill[tileA] ({x},{y}) rectangle ({x+1},{y+1}); \\draw[thick] ({x},{y}) rectangle ({x+1},{y+1});")
        out.append(f"\\node at ({x+0.5},{y+0.5}) {{\\small {phi((x0, y0))}}};")
    for (x0, y0) in Q:
        x, y = x0 - qx + shift, y0 - qy
        out.append(f"\\fill[tileB] ({x},{y}) rectangle ({x+1},{y+1}); \\draw[thick] ({x},{y}) rectangle ({x+1},{y+1});")
        out.append(f"\\node at ({x+0.5},{y+0.5}) {{\\small {phi((x0, y0))}}};")
    out.append(f"\\node[anchor=north] at ({(max(x for x,_ in P)+1)/2},-0.3) {{$P$}};")
    out.append(f"\\node[anchor=north] at ({shift + (max(x for x,_ in Q)-qx+1)/2},-0.3) {{$-P+t$}};")
    y0 = -2.6; x0 = (shift + max(x for x, _ in Q) - qx + 1 - 12) / 2
    for g in range(12):
        col = "tileA" if g in A else "tileB"
        out.append(f"\\fill[{col}] ({x0+g},{y0}) rectangle ({x0+g+1},{y0+1}); \\draw ({x0+g},{y0}) rectangle ({x0+g+1},{y0+1});")
        out.append(f"\\node at ({x0+g+0.5},{y0+0.5}) {{\\small {g}}};")
    out.append(f"\\node[anchor=east] at ({x0-0.2},{y0+0.5}) {{$\\mathbb{{Z}}_{{12}}$}};")
    out.append("\\end{tikzpicture}")
    print(f"uid {uid}: phi(x,y) = {a}x + {b}y mod 12, A = {sorted(A)}, s = {sv}, t = {t}")
    return "\n".join(out)

if __name__ == "__main__":
    for uid in (0, 1, 2, 6):
        W, H = 16, 10
        open(f"figs/net{uid}.tex", "w").write(net(uid))
        open(f"figs/tiling{uid}.tex", "w").write(tikz(tiling(uid, W, H), W, H))
    open("figs/mechanism1.tex", "w").write(mechanism(1))
    print("ok")
