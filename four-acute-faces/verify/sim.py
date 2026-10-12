"""Monte Carlo estimate of P(all four faces acute) for four uniform points on the sphere."""
import numpy as np

rng = np.random.default_rng(0)
n = 1_000_000
P = rng.normal(size=(n, 4, 3))
P /= np.linalg.norm(P, axis=2, keepdims=True)
ok = np.ones(n, dtype=bool)
for missing in range(4):
    face = [i for i in range(4) if i != missing]
    for k in range(3):
        z, x, y = (P[:, face[(k + j) % 3]] for j in range(3))
        ok &= np.einsum("ij,ij->i", x - z, y - z) > 0
print(f"estimate {ok.mean():.5f}  (1/12 = {1/12:.5f}), n = {n}")
