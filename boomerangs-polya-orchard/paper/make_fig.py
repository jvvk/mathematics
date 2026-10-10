"""Write fig_corridor.tex (the corridor arc of Theorem 1 at r = 1/4) and fig_best.tex (the certified arc at
r = 1/6), discs drawn to scale. Asserts each arc's exact reach (verify/certify.py) against the stated value."""
import json
import math
import pathlib
import sys

HERE = pathlib.Path(__file__).resolve().parent
sys.path.insert(0, str(HERE.parent / "verify"))
from certify import reach  # noqa: E402


def t0(r):
    A, K = (1 - r) ** 2, 1 - 3 * r + 3 * r * r
    return r * (1 - r) / (A + math.sqrt(A * A - K * r * (1 - r)))


def arc_points(a, theta, smax, n=160):
    """Points of the ccw arc from O, by turning angle, up to chord length smax."""
    psi_max = 2 * math.asin(min(smax / (2 * a), 1))
    cx, cy = -a * math.sin(theta), a * math.cos(theta)
    start = math.atan2(-cy, -cx)
    return [(cx + a * math.cos(start + psi_max * k / n), cy + a * math.sin(start + psi_max * k / n))
            for k in range(n + 1)]


def picture(name, r, a, theta, smax, box, scale):
    x0, x1, y0, y1 = box
    out = [f"\\begin{{tikzpicture}}[scale={scale}]"]
    for i in range(math.floor(x0), math.ceil(x1) + 1):
        for j in range(math.floor(y0), math.ceil(y1) + 1):
            if (i, j) != (0, 0):
                out.append(f"  \\fill[inkblue!35] ({i},{j}) circle ({r:.4f});")
    pts = arc_points(a, theta, smax)
    out.append("  \\draw[rust, line width=1.2pt] " + " -- ".join(f"({x:.4f},{y:.4f})" for x, y in pts) + ";")
    out.append("  \\fill[black] (0,0) circle (0.06);")
    return out


r = 0.25
t = t0(r) * (1 + 1e-9)
alpha = 2 * math.atan(t)
a = (1 - r) / (1 - math.cos(alpha))
theta = math.pi / 2 - alpha
claimed = 2 * (1 - r) / t - (1 - r)
exact_c = float(reach(a, theta, r, claimed + 3))
exact = exact_c
assert exact >= claimed - 1e-9 and claimed > 4 / r - 10, (exact, claimed)
out = picture("corridor", r, a, theta, exact, (-1, 2, -1, math.ceil(exact) + 1), 0.62)
out.insert(1, f"  \\draw[gray, dashed] ({r},-1) -- ({r},{math.ceil(exact) + 1}); "
              f"\\draw[gray, dashed] ({1 - r},-1) -- ({1 - r},{math.ceil(exact) + 1});")
out.append(f"  \\draw[gray] (2.6,{exact:.3f}) -- (2.9,{exact:.3f}) node[right, font=\\small] "
           f"{{reach ${exact:.2f}$}};")
out.append(f"  \\draw[gray] (2.6,{4 / r - 10:.3f}) -- (2.9,{4 / r - 10:.3f}) node[right, font=\\small] {{$4/r-10={4 / r - 10:.0f}$}};")
out.append("\\end{tikzpicture}")
(HERE / "fig_corridor.tex").write_text("\n".join(out) + "\n")

cert = next(c for c in json.loads((HERE.parent / "verify" / "certificates.json").read_text()) if c["inv_r"] == 6.0)
r = 1 / 6
exact = float(reach(cert["a"], cert["theta"], r, cert["reach"] + 3))
assert exact >= cert["reach"] - 1e-9
pts = arc_points(cert["a"], cert["theta"], exact)
xs, ys = [p[0] for p in pts], [p[1] for p in pts]
out = picture("best", r, cert["a"], cert["theta"], exact, (min(xs) - 1, max(xs) + 1, min(ys) - 1, max(ys) + 1), 0.24)
out.append("\\end{tikzpicture}")
(HERE / "fig_best.tex").write_text("\n".join(out) + "\n")
print(f"corridor r=1/4: reach >= {claimed:.4f} (exact first entry {exact_c:.4f}); best r=1/6 reach {exact:.4f}")
