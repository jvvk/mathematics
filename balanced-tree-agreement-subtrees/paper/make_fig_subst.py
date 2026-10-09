"""Figure: (a) two balanced trees on 4 leaves with MAST 2; (b) substitution S = S°[A].
Also checks: the n=4 pair substituted into itself gives 16-leaf balanced trees with MAST 4 (recurrence (1))."""
from functools import lru_cache
from pathlib import Path

import matplotlib

matplotlib.use("Agg")
import matplotlib.pyplot as plt
from matplotlib.patches import Polygon


def leaves(t):
    return [t] if not isinstance(t, tuple) else leaves(t[0]) + leaves(t[1])


@lru_cache(None)
def mast(S, T):  # recurrence (1) of the paper, on trees sharing a label set
    if not isinstance(S, tuple) or not isinstance(T, tuple):
        a = set(leaves(S)) & set(leaves(T))
        return min(1, len(a)) if not (isinstance(S, tuple) or isinstance(T, tuple)) else (1 if a else 0)
    SL, SR = S; TL, TR = T
    return max(mast(SL, TL) + mast(SR, TR), mast(SL, TR) + mast(SR, TL),
               mast(S, TL), mast(S, TR), mast(SL, T), mast(SR, T))


S4, T4 = ((1, 2), (3, 4)), ((1, 3), (2, 4))
assert mast(S4, T4) == 2


def subst(outer, inner):
    if not isinstance(outer, tuple):
        z = outer
        def rel(t):
            return (rel(t[0]), rel(t[1])) if isinstance(t, tuple) else 10 * z + t
        return rel(inner)
    return (subst(outer[0], inner), subst(outer[1], inner))


S16, T16 = subst(S4, S4), subst(T4, T4)
assert sorted(leaves(S16)) == sorted(leaves(T16)) and len(leaves(S16)) == 16
print("mast of substituted 16-leaf pair:", mast(S16, T16))

fig, (ax1, ax2) = plt.subplots(1, 2, figsize=(6.6, 2.6), gridspec_kw={"width_ratios": [1.15, 1]})


def draw(ax, t, x0, x1, y, dy, col="#1b1b1b"):
    if not isinstance(t, tuple):
        ax.text((x0 + x1) / 2, y - 0.18, str(t), ha="center", va="top", fontsize=12)
        return (x0 + x1) / 2
    xm = (x0 + x1) / 2
    xl = draw(ax, t[0], x0, xm, y - dy, dy, col); xr = draw(ax, t[1], xm, x1, y - dy, dy, col)
    xc = (xl + xr) / 2
    ax.plot([xl, xc, xr], [y - dy, y, y - dy], color=col, lw=1.6)
    return xc


draw(ax1, S4, 0, 2, 2, 1, "#2563a8"); draw(ax1, T4, 2.6, 4.6, 2, 1, "#c0392b")
ax1.text(1, 2.25, r"$S$", ha="center", fontsize=13, color="#2563a8")
ax1.text(3.6, 2.25, r"$T$", ha="center", fontsize=13, color="#c0392b")
ax1.set_title("(a) no three leaves agree", fontsize=11)
ax1.set_xlim(-0.2, 4.8); ax1.set_ylim(-0.4, 2.6); ax1.axis("off")
xs = [0.5, 1.5, 2.5, 3.5]
for (a, b), yv in [((xs[0], xs[1]), 1), ((xs[2], xs[3]), 1)]:
    ax2.plot([a, (a + b) / 2, b], [yv, yv + 0.8, yv], color="#1b1b1b", lw=1.6)
ax2.plot([1.0, 2.0, 3.0], [1.8, 2.5, 1.8], color="#1b1b1b", lw=1.6)
for i, x in enumerate(xs, 1):
    ax2.add_patch(Polygon([[x, 1], [x - 0.42, 0.05], [x + 0.42, 0.05]], closed=True, fc="#e8eef7", ec="#2563a8", lw=1.2))
    ax2.text(x, 0.4, rf"$A_{{z_{i}}}$", ha="center", fontsize=11, color="#2563a8")
ax2.text(2.0, 2.65, r"$S^\circ$", ha="center", fontsize=13)
ax2.set_title(r"(b) $S=S^\circ[A]$", fontsize=11)
ax2.set_xlim(-0.1, 4.1); ax2.set_ylim(-0.1, 3.1); ax2.axis("off")
fig.tight_layout()
fig.savefig(Path(__file__).parent / "fig_subst.pdf", bbox_inches="tight"); fig.savefig(Path(__file__).parent / "fig_subst.png", dpi=170, bbox_inches="tight")
