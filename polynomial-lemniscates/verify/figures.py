"""Draw the two figures of the paper into ../paper/figs (matplotlib, vector PDF).

Figure 1: the Bernoulli lemniscates |z^2 - 1| = 1 and |(z - 1)^2 - 1| = 1 and their six common points.
Figure 2: the Z-coordinates of the eight solutions of f1(Z) f1(W) = 1, f2(Z) f2(W) = 1
          (z and conj z made independent), the six real ones, the sigma-pair, and m = 1/2.
"""
import pathlib

import matplotlib
matplotlib.use("pdf")
import matplotlib.pyplot as plt
import mpmath as mp
import numpy as np

OUT = pathlib.Path(__file__).resolve().parent.parent / "paper" / "figs"
OUT.mkdir(parents=True, exist_ok=True)
plt.rcParams.update({"font.family": "serif", "mathtext.fontset": "cm", "font.size": 10})

s23, s3 = np.sqrt(2 / 3), 1 / np.sqrt(12)
v = np.sqrt(4 * np.sqrt(2) - 5) / 2
six = [(0.5, v), (0.5, -v), (0.5 + s23, s3), (0.5 + s23, -s3), (0.5 - s23, s3), (0.5 - s23, -s3)]

x = np.linspace(-1.9, 2.9, 1400)
y = np.linspace(-1.2, 1.2, 800)
X, Y = np.meshgrid(x, y)
Zg = X + 1j * Y


def base(ax):
    ax.contour(X, Y, np.abs(Zg**2 - 1), [1], colors="#1f4e9a", linewidths=1.3)
    ax.contour(X, Y, np.abs((Zg - 1) ** 2 - 1), [1], colors="#b5432b", linewidths=1.3)
    ax.set_aspect("equal")
    ax.axhline(0, color="0.8", lw=0.5, zorder=0)
    ax.set_xticks([-1, 0, 1, 2])
    ax.set_yticks([-1, 0, 1])


fig, ax = plt.subplots(figsize=(4.6, 2.5))
base(ax)
ax.plot(*zip(*six), "ko", ms=4.5)
for (a, b) in [(-1, 0), (1, 0)]:
    ax.plot(a, b, "+", color="#1f4e9a", ms=6)
for (a, b) in [(0, 0), (2, 0)]:
    ax.plot(a, b, "x", color="#b5432b", ms=5)
fig.tight_layout()
fig.savefig(OUT / "six.pdf")

# Figure 2: all eight solutions (Z, W) of z^2-1 and (z-1)^2-1 with independent W.
mp.mp.dps = 40
sols = []
# Solve directly: f1(Z) f1(W) = 1, f2(Z) f2(W) = 1, f1 = t^2 - 1, f2 = (t-1)^2 - 1.
def F(a, b):
    return [(a**2 - 1) * (b**2 - 1) - 1, ((a - 1) ** 2 - 1) * ((b - 1) ** 2 - 1) - 1]
seeds = [complex(p, q) for p in np.linspace(-2, 3, 11) for q in np.linspace(-1.5, 1.5, 7)]
for s in seeds:
    for t in seeds[::5]:
        try:
            r = mp.findroot(F, (mp.mpc(s), mp.mpc(t)))
        except Exception:
            continue
        a, b = complex(r[0]), complex(r[1])
        if all(abs(a - c) + abs(b - d) > 1e-9 for c, d in sols):
            sols.append((a, b))
assert len(sols) == 8, len(sols)
real = [p for p in sols if abs(p[1] - np.conj(p[0])) < 1e-9]
pair = [p for p in sols if abs(p[1] - np.conj(p[0])) >= 1e-9]
assert len(real) == 6 and len(pair) == 2
m = 0.5
T = sum((a - m) * (b - m) for a, b in sols)
assert abs(T + 2) < 1e-9

fig, ax = plt.subplots(figsize=(4.6, 2.9))
base(ax)
ax.plot([p[0].real for p in real], [p[0].imag for p in real], "ko", ms=4.5, label="real solutions $(z,\\bar z)$")
ax.plot([p[0].real for p in pair], [p[0].imag for p in pair], "o", mfc="white", mec="k", ms=6,
        label="$Z$ of the $\\sigma$-pair")
ax.plot(m, 0, "k*", ms=8, label="$m=1/2$")
ax.legend(loc="lower center", bbox_to_anchor=(0.5, 1.0), ncol=3, fontsize=7.5, frameon=False,
          handletextpad=0.3, columnspacing=1.0)
ax.set_ylim(-1.25, 1.25)
fig.tight_layout()
fig.savefig(OUT / "pairing.pdf")
for a, b in pair:
    print("pair Z =", a, " W =", b, " contribution (Z-m)(W-m) =", (a - m) * (b - m))
print("sum over real solutions of |z - m|^2 =", sum(abs(a - m) ** 2 for a, b in real))
print("total =", T)
