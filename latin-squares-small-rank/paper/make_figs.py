"""Figure data for the note: the factorisation C = X Y^T of the centred 4 x 4 XOR square in the plane,
and the 6 x 6 rank-4 square. Asserts every claim the figures make."""
import numpy as np
from pathlib import Path

OUT = Path(__file__).resolve().parent / "figs"
V = np.array([[1 + (i ^ j) for j in range(4)] for i in range(4)], dtype=float)
n = 4
C = 2 * V - (n + 1)
# orthonormal basis of the column space of C (it lies in the column space of V and is orthogonal to 1)
U, s, _ = np.linalg.svd(C)
d = int((s > 1e-9).sum())
assert d == 2
U = U[:, :d]
# rotate so that x_1 points along the first axis (any orthonormal basis works)
th = np.arctan2(U[0, 1], U[0, 0]); R = np.array([[np.cos(th), np.sin(th)], [-np.sin(th), np.cos(th)]])
X = U @ R.T                    # rows x_i
Y = C.T @ X                    # rows y_j
assert np.allclose(X @ Y.T, C)
assert np.isclose((X ** 2).sum(), d)                          # sum |x_i|^2 = d
assert np.allclose((Y ** 2).sum(axis=1), n * (n * n - 1) / 3)  # |y_j|^2 = S2 = 20
assert np.allclose(np.ones(4) @ C, 0)
lines = []
for i, (a, b) in enumerate(X):
    lines.append(f"\\coordinate (x{i+1}) at ({a:.4f},{b:.4f});")
for j, (a, b) in enumerate(Y):
    lines.append(f"\\coordinate (y{j+1}) at ({a / 4:.4f},{b / 4:.4f});")   # y scaled by 1/4 to fit
(OUT / "xor4.tex").write_text("\n".join(lines) + "\n")
print("C =\n", C.astype(int)); print("x_i =", np.round(X, 3).tolist()); print("y_j =", np.round(Y, 3).tolist())
print("|x_i|^2 =", np.round((X ** 2).sum(axis=1), 3).tolist())
