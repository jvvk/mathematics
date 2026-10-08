"""Figure: the mex sequence from 1,1,1,0,1,0,1,1, coloured by residue mod 5 (computed from the definition)."""
from pathlib import Path

import matplotlib

matplotlib.use("Agg")
import matplotlib.pyplot as plt

N = 150
a = [1, 1, 1, 0, 1, 0, 1, 1]
while len(a) < N:
    n = len(a) - 1
    s = {a[i] + a[n - i] for i in range(n + 1)}
    m = 0
    while m in s:
        m += 1
    a.append(m)
# the closed form of the theorem, as an independent check
def y(b):
    if b < 3:
        return [1, 1, 3][b]
    k, j = divmod(b - 3, 3)
    return [4 * k + 2, 4 * k + 5, 4 * k + 4][j]
for n in range(1, N):
    b, j = divmod(n, 5)
    want = 0 if j in (0, 3) else (y(b) if j in (1, 2) else ([1, 3, 3][b] if b < 3 else 2))
    assert a[n] == want, (n, a[n], want)
cols = {0: "#9a9a9a", 3: "#9a9a9a", 1: "#c0392b", 2: "#e67e22", 4: "#2563a8"}
labs = {0: r"$n\equiv0,3$: $0$ (except $a_0=1$)", 1: r"$n\equiv1$", 2: r"$n\equiv2$ (same value)", 4: r"$n\equiv4$: settles at $2$"}
fig, ax = plt.subplots(figsize=(6.4, 2.2))
for j in (0, 3, 1, 2, 4):
    xs = [n for n in range(N) if n % 5 == j]
    ax.scatter(xs, [a[n] for n in xs], s=10 if j != 2 else 22, color=cols[j], label=labs.get(j),
               marker="o" if j != 2 else "s", facecolors="none" if j == 2 else cols[j], zorder=3 if j != 2 else 2)
ax.set_xlabel(r"$n$"); ax.set_ylabel(r"$a_n$")
ax.spines[["top", "right"]].set_visible(False)
ax.legend(frameon=False, fontsize=8, loc="upper left")
fig.tight_layout()
fig.savefig(Path(__file__).parent / "fig_sequence.pdf"); fig.savefig(Path(__file__).parent / "fig_sequence.png", dpi=170)
print("closed form verified for n <", N, "; a_149 =", a[149])
