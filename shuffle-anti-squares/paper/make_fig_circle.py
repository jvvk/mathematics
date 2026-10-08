"""Figure: the anti-square U_0 drawn as a circular word, with its two long gaps and two clusters."""
from pathlib import Path

import matplotlib
import numpy as np

matplotlib.use("Agg")
import matplotlib.pyplot as plt

K = 9  # k = 0
word = "0" * K + "1" + "0" * 5 + "11" + "0" * K + "1" + "00" + "1" + "0" + "111"
assert len(word) == 34
# brute-force check (independent of the paper): no rotation of U_0 is a shuffle square
from functools import lru_cache


def is_shuffle_square(w):
    n = len(w)
    if n % 2:
        return False

    @lru_cache(None)
    def go(i, pending):  # pending: letters assigned to A not yet matched by B
        if i == n:
            return pending == ""
        c = w[i]
        if len(pending) < (n - i) and go(i + 1, pending + c):  # give to A
            return True
        return bool(pending) and pending[0] == c and go(i + 1, pending[1:])  # give to B, matching A
    return go(0, "")


assert not any(is_shuffle_square(word[r:] + word[:r]) for r in range(34)), "U_0 should be an anti-square"
assert is_shuffle_square("1100") and not is_shuffle_square("0110")
n = len(word)
th = np.pi / 2 - 2 * np.pi * (np.arange(n) + 0.5) / n
fig, ax = plt.subplots(figsize=(4.2, 4.2))
ax.plot(np.cos(np.linspace(0, 2 * np.pi, 300)), np.sin(np.linspace(0, 2 * np.pi, 300)), color="#cfcfcf", lw=1, zorder=0)
for t, ch in zip(th, word):
    ax.plot(np.cos(t), np.sin(t), "o", ms=8, color="#1b1b1b" if ch == "1" else "white", mec="#1b1b1b", zorder=2)


def arc_label(i0, i1, text, r=1.28, col="#2563a8"):
    ts = th[i0:i1 + 1]
    ax.plot(1.14 * np.cos(ts), 1.14 * np.sin(ts), color=col, lw=2.2)
    tm = ts.mean()
    ax.text(r * np.cos(tm), r * np.sin(tm), text, ha="center", va="center", fontsize=15, color=col)


arc_label(0, K - 1, r"$G$ ($K$ zeros)", r=1.45)
arc_label(K, K + 7, r"$C_1$", col="#c0392b")
arc_label(K + 8, 2 * K + 7, r"$G'$ ($K$ zeros)", r=1.45)
arc_label(2 * K + 8, n - 1, r"$C_2$", col="#c0392b")
ax.set_xlim(-1.75, 1.75); ax.set_ylim(-1.75, 1.75); ax.set_aspect("equal"); ax.axis("off")
fig.tight_layout()
fig.savefig(Path(__file__).parent / "fig_circle.pdf", bbox_inches="tight"); fig.savefig(Path(__file__).parent / "fig_circle.png", dpi=170, bbox_inches="tight")
print("U_0 verified anti-square by brute force; 0110 not, 1100 is a shuffle square")
