"""Figure: the overlap table x_1..x_4 and the six cases of recurrence (1) that make up Phi."""
from pathlib import Path

import matplotlib

matplotlib.use("Agg")
import matplotlib.pyplot as plt
from matplotlib.patches import Rectangle

cells = {(0, 0): "$x_1$", (0, 1): "$x_2$", (1, 0): "$x_3$", (1, 1): "$x_4$"}
groups = [("diagonal", [(0, 0), (1, 1)], r"$4^c(x_1^a+x_4^a)$"), ("antidiagonal", [(0, 1), (1, 0)], r"$4^c(x_2^a+x_3^a)$"),
          ("row $S_L$", [(0, 0), (0, 1)], r"$2^c(x_1+x_2)^a$"), ("row $S_R$", [(1, 0), (1, 1)], r"$2^c(x_3+x_4)^a$"),
          ("column $T_L$", [(0, 0), (1, 0)], r"$2^c(x_1+x_3)^a$"), ("column $T_R$", [(0, 1), (1, 1)], r"$2^c(x_2+x_4)^a$")]
fig, axes = plt.subplots(1, 6, figsize=(7.4, 1.9))
for ax, (name, hl, term) in zip(axes, groups):
    for (r, c), lab in cells.items():
        on = (r, c) in hl
        ax.add_patch(Rectangle((c, 1 - r), 1, 1, fc="#f6d5c9" if on else "white", ec="#1b1b1b", lw=1))
        ax.text(c + 0.5, 1.5 - r, lab, ha="center", va="center", fontsize=11)
    ax.text(1, -0.35, term, ha="center", va="center", fontsize=9)
    ax.set_xlim(-0.05, 2.05); ax.set_ylim(-0.6, 2.35); ax.set_aspect("equal"); ax.axis("off")
axes[0].text(-0.15, 1.5, "$S_L$", ha="right", va="center", fontsize=9)
axes[0].text(-0.15, 0.5, "$S_R$", ha="right", va="center", fontsize=9)
axes[0].text(0.5, 2.15, "$T_L$", ha="center", fontsize=9); axes[0].text(1.5, 2.15, "$T_R$", ha="center", fontsize=9)
fig.tight_layout(w_pad=0.6)
fig.savefig(Path(__file__).parent / "fig_grid.pdf", bbox_inches="tight"); fig.savefig(Path(__file__).parent / "fig_grid.png", dpi=170, bbox_inches="tight")
