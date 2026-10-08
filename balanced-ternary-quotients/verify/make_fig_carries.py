"""Schematic of the carry set S_k for n = 4*3^k + 5 (positive half), transcribed from Table 1."""
from pathlib import Path

import matplotlib

matplotlib.use("Agg")
import matplotlib.pyplot as plt
from matplotlib.patches import Arc, FancyArrowPatch

fig, ax = plt.subplots(figsize=(5.0, 3.9))
rows = ["k-1", "k-2", None, "1", "0"]          # None marks the ellipsis
y = {lab: 4 - r for r, lab in enumerate(rows)}
X2, X4 = 0.0, 3.2
BLUE, GREY, RED = "#2563a8", "#7a7a7a", "#c0392b"


def node(x, yy, text, col="black"):
    ax.text(x, yy, text, ha="center", va="center", fontsize=12, color=col,
            bbox=dict(boxstyle="round,pad=0.3", fc="white", ec=col, lw=1))


def arrow(p, q, col=BLUE, ls="-", rad=0.0, lw=1.4):
    ax.add_patch(FancyArrowPatch(p, q, arrowstyle="-|>", mutation_scale=12, color=col, ls=ls, lw=lw,
                                 connectionstyle=f"arc3,rad={rad}", shrinkA=16, shrinkB=16))


for lab in rows:
    if lab is None:
        ax.text(X2, y[lab], r"$\vdots$", ha="center", va="center", fontsize=14)
        ax.text(X4, y[lab], r"$\vdots$", ha="center", va="center", fontsize=14)
        continue
    node(X2, y[lab], rf"$c-2\cdot3^{{{lab}}}$")
    node(X4, y[lab], rf"$c-4\cdot3^{{{lab}}}$")
for a, b in [("k-1", "k-2"), ("1", "0")]:
    arrow((X2, y[a]), (X2, y[b])); arrow((X4, y[a]), (X4, y[b]))
for a in ["k-2"]:
    arrow((X2, y[a]), (X2, y[None] + 0.25)); arrow((X4, y[a]), (X4, y[None] + 0.25))
arrow((X2, y[None] - 0.25), (X2, y["1"])); arrow((X4, y[None] - 0.25), (X4, y["1"]))
node(-2.3, 5.2, r"$0$")
arrow((-2.3, 5.2), (X2, y["k-1"]))
node(X2, -1.4, r"$c$")
arrow((X2, y["0"]), (X2, -1.4))
ax.add_patch(Arc((X2 + 0.62, -1.4), 0.55, 0.55, theta1=-150, theta2=150, color=BLUE, lw=1.4))
ax.add_patch(FancyArrowPatch((X2 + 0.40, -1.24), (X2 + 0.31, -1.33), arrowstyle="-|>", mutation_scale=10, color=BLUE, lw=1.2))
ax.text(X4, -1.4, r"$-(c-4\cdot3^{k-1})$", ha="center", va="center", fontsize=11, color=RED)
arrow((X2, y["0"]), (X4 - 0.2, -1.4), col=RED, ls="--", lw=1.1)
arrow((X4, y["0"]), (X4, -1.4), col=RED, ls="--", lw=1.1)
arrow((-2.3, 5.2), (-2.3, 3.2), col=RED, ls="--", lw=1.1)
ax.text(-2.3, 2.9, r"$-(c-2\cdot3^{k-1})$", ha="center", fontsize=11, color=RED)

ax.set_xlim(-3.4, 5.6); ax.set_ylim(-2.1, 5.7); ax.axis("off")
fig.tight_layout()
fig.savefig(Path(__file__).parent / "fig_carries.pdf"); fig.savefig(Path(__file__).parent / "fig_carries.png", dpi=170)
