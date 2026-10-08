"""Exact reduction of the limit model for general p (Corollary 3 and Section 6 of the paper):
P_p = p tan(pi/p) * E_p / 6,  E_p = E[ |det A| 1{e_rho in cone(rows of A)} ],
A = 4x4 matrix with rows (1, u_k, -sigma), k uniform in {0..p-1}, sigma uniform in [-1,1], 4 independent rows.
Monte Carlo for E_p. For odd p this is Corollary 3. For even p the tolerance in the cone test also accepts the tuples
whose tetrahedron has the origin on a face (two points on one edge, one on the opposite edge), which Corollary 3
excludes; empirically their contribution equals the segment term 8/(3 p^2), so the printed value is the full p_p
(p = 4: 0.2486 +- 0.0010; p = 6: 0.1929 +- 0.0006). That identity is observed here, not proved.
Usage: general_p.py p samples seed"""
import os, sys, signal, math, numpy as np
def _stop(*_): raise TimeoutError
signal.signal(signal.SIGALRM, _stop); signal.alarm(int(os.environ.get("TIME_LIMIT", "0")))
p, N, seed = int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3]); rng = np.random.default_rng(seed)
tot = 0.0; tot2 = 0.0; done = 0
try:
    while done < N:
        m = min(200000, N - done)
        k = rng.integers(0, p, (m, 4)); s = rng.uniform(-1, 1, (m, 4)); a = 2 * np.pi * k / p
        A = np.stack([np.ones((m, 4)), np.cos(a), np.sin(a), -s], -1)          # (m, 4 rows, 4 cols)
        det = np.linalg.det(A); good = np.abs(det) > 1e-12
        lam = np.zeros((m, 4)); lam[good] = np.linalg.solve(np.transpose(A[good], (0, 2, 1)), np.tile([1., 0, 0, 0], (good.sum(), 1))[..., None])[..., 0]
        f = np.where(good & (lam >= -1e-12).all(1), np.abs(det), 0.0)
        tot += f.sum(); tot2 += (f * f).sum(); done += m
except Exception as e:
    print("stopped:", type(e).__name__)
E = tot / done; se = math.sqrt(tot2 / done - E * E) / math.sqrt(done)
c = p * math.tan(math.pi / p) / 6
print(f"p={p} samples={done} E_p={E:.5f} P_p={c*E:.5f} +- {c*se:.5f}")
