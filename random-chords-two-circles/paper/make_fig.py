"""Figure for the note: a line meeting two disjoint circles, its four point pairs and the chord identity."""

from pathlib import Path

import matplotlib
import numpy as np

matplotlib.use("Agg")
import matplotlib.pyplot as plt

a, D = 0.6, 2.4
P, Q = np.array([-D, 0.0]), np.array([0.0, 0.0])
phi = np.deg2rad(68)
m = np.array([np.cos(phi), np.sin(phi)])
mp = np.array([-m[1], m[0]])
p = -0.6
RED, GREEN, BLUE, GREY = "#c0392b", "#1e8449", "#2563a8", "#8a8a8a"

fig, ax = plt.subplots(figsize=(5.6, 3.0))
t = np.linspace(0, 2 * np.pi, 400)
ax.plot(P[0] + a * np.cos(t), a * np.sin(t), color=RED, lw=1.8)
ax.plot(np.cos(t), np.sin(t), color=GREEN, lw=1.8)
s = np.linspace(-1.2, 3.4, 2)
line = np.outer(np.ones_like(s), p * m) + np.outer(s, mp)
ax.plot(line[:, 0], line[:, 1], color=BLUE, lw=1.6)
ax.annotate(
    r"$\ell$", line[0], (4, -14), textcoords="offset points", fontsize=15, color=BLUE
)


def meet(c, r):
    x = (p - m @ c) / r
    h = np.sqrt(1 - x * x)
    return [c + r * (x * m + sg * h * mp) for sg in (1, -1)], x


As, xA = meet(P, a)
Bs, xB = meet(Q, 1.0)
for pt, lab, col, off in [
    (As[0], r"$A_+$", RED, (-24, 4)),
    (As[1], r"$A_-$", RED, (6, -6)),
    (Bs[0], r"$B_+$", GREEN, (-26, 2)),
    (Bs[1], r"$B_-$", GREEN, (6, -4)),
]:
    ax.plot(*pt, "o", color=col, ms=6)
    ax.annotate(lab, pt, off, textcoords="offset points", fontsize=15)
for c, lab, col in [(P, "P", RED), (Q, "Q", GREEN)]:
    foot = c + (p - m @ c) * m
    ax.plot([c[0], foot[0]], [c[1], foot[1]], color=col, lw=1.0, ls="--")
    ax.plot(*c, "k.", ms=6)
    ax.annotate(lab, c, (-14, -12), textcoords="offset points", fontsize=15)
    ax.plot(*foot, "s", color=GREY, ms=4)
ax.set_aspect("equal")
ax.set_xlim(-3.4, 1.5)
ax.set_ylim(-1.25, 1.2)
ax.axis("off")
fig.tight_layout()
fig.savefig(Path(__file__).parent / "fig_chords.pdf")
fig.savefig(Path(__file__).parent / "fig_chords.png", dpi=170)
print(f"x_A = {xA:.3f}, x_B = {xB:.3f}")
