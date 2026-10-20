"""Coverage map: count curved Spectres over every pixel of four period cells (an illustration, not a proof).

Writes coverage_map.png (with a caption line) next to this script and ../paper/coverage_map.png (no title)
for the paper. Needs numpy and matplotlib."""
import json
from pathlib import Path
import numpy as np
import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
from matplotlib.path import Path as MPath
from matplotlib.colors import ListedColormap, BoundaryNorm

here = Path(__file__).resolve().parent
data = json.loads((here / "certificate.json").read_text())
z = np.exp(1j * np.pi / 6)
D = [0, 10, 1, 3, 0, 2, 5, 7, 4, 6, 6, 8, 11, 9]
P = np.r_[0, np.cumsum([z**d for d in D])]
curve = []
for i, d in enumerate(D):  # same edge curve as codex/illustrate.py
    t = np.linspace(0, 1, 41, endpoint=False)
    s = (-1) ** i
    c1, c2 = 0.33 + 0.6j * s, 0.67 + 0.6j * s
    curve.extend(P[i] + z**d * (3 * (1 - t) ** 2 * t * c1 + 3 * (1 - t) * t * t * c2 + t**3))
curve = np.array(curve)
a, b = z * z + z**3, -2 - z - z**3
v, w = 3 + z + 2 * z * z + 3 * z**3, -4 - 3 * z + 3 * z * z + z**3
M = np.array([[v.real, w.real], [v.imag, w.imag]])

# Window: a rectangle around two-by-two period cells.
corners = np.array([0, v, w, v + w, 2 * v, 2 * w, 2 * v + 2 * w, 2 * v + w, v + 2 * w])
x0, x1 = corners.real.min(), corners.real.max()
y0, y1 = corners.imag.min(), corners.imag.max()
nx = 700
ny = int(nx * (y1 - y0) / (x1 - x0))
X, Y = np.meshgrid(np.linspace(x0, x1, nx), np.linspace(y0, y1, ny))
pts = np.c_[X.ravel(), Y.ravel()]
count = np.zeros(len(pts), dtype=np.int16)
outlines = []
for r, x, y, _ in data["placements"]:
    base = z**r * curve + x * a + y * b
    uv = np.linalg.solve(M, [base.mean().real, base.mean().imag])
    base -= np.floor(uv[0]) * v + np.floor(uv[1]) * w
    for j in range(-2, 5):
        for k in range(-2, 5):
            c = base + j * v + k * w
            if c.real.max() < x0 or c.real.min() > x1 or c.imag.max() < y0 or c.imag.min() > y1:
                continue
            poly = np.c_[c.real, c.imag]
            m = (pts[:, 0] >= poly[:, 0].min()) & (pts[:, 0] <= poly[:, 0].max()) & \
                (pts[:, 1] >= poly[:, 1].min()) & (pts[:, 1] <= poly[:, 1].max())
            count[m] += MPath(np.r_[poly, poly[:1]]).contains_points(pts[m])
            outlines.append(poly)
vals, freq = np.unique(count, return_counts=True)
print("pixel counts:", dict(zip(vals.tolist(), freq.tolist())))

grid = count.reshape(ny, nx).astype(float)
cmap = ListedColormap(["#b91c1c", "#dbeafe", "#f59e0b"])  # below 12, exactly 12, above 12
norm = BoundaryNorm([-0.5, 11.5, 12.5, 99], cmap.N)
fig, ax = plt.subplots(figsize=(8, 8 * ny / nx), layout="constrained")
ax.imshow(grid, origin="lower", extent=(x0, x1, y0, y1), cmap=cmap, norm=norm, interpolation="nearest")
for poly in outlines:
    ax.plot(*np.r_[poly, poly[:1]].T, color="#1e3a5f", lw=0.25, alpha=0.35)
hi = max(outlines, key=lambda q: -abs(q.mean(axis=0) - [(v + w).real, (v + w).imag]).sum())  # tile nearest the centre
ax.fill(*hi.T, color="#0e7490", alpha=0.55); ax.plot(*np.r_[hi, hi[:1]].T, color="#0e7490", lw=1.6)
for j in range(3):  # period lattice
    ax.plot([(j * v).real, (j * v + 2 * w).real], [(j * v).imag, (j * v + 2 * w).imag], color="#111827", lw=1.4)
    ax.plot([(j * w).real, (j * w + 2 * v).real], [(j * w).imag, (j * w + 2 * v).imag], color="#111827", lw=1.4)
ax.set_xlim(x0, x1); ax.set_ylim(y0, y1); ax.set_aspect("equal"); ax.axis("off")
share = freq[vals == 12].sum() / len(count)
fig.savefig(here.parent / "paper" / "coverage_map.png", dpi=170, facecolor="white")
ax.set_title(f"Spectres covering each point, sampled on a {nx}x{ny} grid: 12 at {100*share:.0f}% of points\n"
             "(pale blue = exactly 12; red/amber would mark fewer/more; black lines = period lattice; one Spectre shaded)", fontsize=10)
fig.savefig(here / "coverage_map.png", dpi=170, facecolor="white")
assert set(vals.tolist()) == {12}, "a pixel is not covered exactly 12 times"
