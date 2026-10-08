"""Figure: Dan's configuration (radii 1/2, 1, 2), one line AB and one line BC, and a second circle about O."""
from pathlib import Path

import matplotlib
import numpy as np

matplotlib.use("Agg")
import matplotlib.pyplot as plt

r = 2.0
a, b, c = 1 / r, 1.0, r
P, Q, O = np.array([-(a + b), 0.0]), np.array([0.0, 0.0]), np.array([b + c, 0.0])
RED, GREEN, BLACK, BLUE, ORANGE = "#c0392b", "#1e8449", "#1b1b1b", "#2563a8", "#b9770e"
fig, ax = plt.subplots(figsize=(5.6, 2.9))
t = np.linspace(0, 2 * np.pi, 400)
for ctr, rad, col, ls in [(P, a, RED, "-"), (Q, b, GREEN, "-"), (O, c, BLACK, "-"), (O, 1.2, GREY := "#8a8a8a", ":")]:
    ax.plot(ctr[0] + rad * np.cos(t), ctr[1] + rad * np.sin(t), color=col, lw=1.6, ls=ls)
A = P + a * np.array([np.cos(np.deg2rad(140)), np.sin(np.deg2rad(140))])
B = Q + b * np.array([np.cos(np.deg2rad(-60)), np.sin(np.deg2rad(-60))])
C = Q + b * np.array([np.cos(np.deg2rad(110)), np.sin(np.deg2rad(110))])
for U, V, col in [(A, B, BLUE), (B, C, ORANGE)]:
    d = (V - U) / np.linalg.norm(V - U)
    seg = np.array([U - 1.2 * d, V + 4.2 * d])
    ax.plot(seg[:, 0], seg[:, 1], color=col, lw=1.4)
for pt, lab, col, off in [(A, r"$A$", RED, (-14, 4)), (B, r"$B$", GREEN, (4, -14)), (C, r"$C$", GREEN, (-14, 4))]:
    ax.plot(*pt, "o", color=col, ms=6)
    ax.annotate(lab, pt, off, textcoords="offset points", fontsize=14)
for pt, lab in [(P, "P"), (Q, "Q"), (O, "O")]:
    ax.plot(*pt, "k.", ms=5)
    ax.annotate(lab, pt, (4, -14), textcoords="offset points", fontsize=14)
ax.set_aspect("equal")
ax.set_xlim(-2.2, 5.2)
ax.set_ylim(-2.3, 2.3)
ax.axis("off")
fig.tight_layout()
fig.savefig(Path(__file__).parent / "fig_config.pdf")
fig.savefig(Path(__file__).parent / "fig_config.png", dpi=170)
