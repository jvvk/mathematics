"""Even-p formula (Corollary 3 of the paper): P_p = p tan(pi/p) E[Vol T 1{0 in int T}] + 8/(3 p^2) for even p (no extra term for odd p).
Nondegenerate part: 4 iid points on prism edges; tuples containing a degenerate triple (two points on edge k, one on the
opposite edge k + p/2: its face plane contains the axis, so 0 lies on it) are EXCLUDED by labels, not by floating signs;
interior test uses a relative tolerance. Usage: even_p.py p samples seed"""
import os, sys, signal, math, numpy as np
def _stop(*_): raise TimeoutError
signal.signal(signal.SIGALRM, _stop); signal.alarm(int(os.environ.get("TIME_LIMIT", "0")))
p, N, seed = map(int, sys.argv[1:4]); rng = np.random.default_rng(seed)
def vol(Y): return np.einsum('mi,mi->m', Y[:, 1] - Y[:, 0], np.cross(Y[:, 2] - Y[:, 0], Y[:, 3] - Y[:, 0])) / 6
tot = tot2 = 0.0; done = 0
while done < N:
    m = min(200000, N - done); k = rng.integers(0, p, (m, 4)); a = 2 * np.pi * k / p
    X = np.stack([np.cos(a), np.sin(a), rng.uniform(-1, 1, (m, 4))], -1); V = vol(X)
    inside = np.ones(m, bool)
    for i in range(4):
        Y = X.copy(); Y[:, i] = 0; inside &= vol(Y) * V > 1e-12 * V * V
    degen = np.zeros(m, bool)
    if p % 2 == 0:
        for e in range(p):   # two labels e and one label e + p/2 among the four
            ce = (k == e).sum(1); co = (k == (e + p // 2) % p).sum(1); degen |= (ce >= 2) & (co >= 1)
    f = np.where(inside & ~degen, np.abs(V), 0.0); tot += f.sum(); tot2 += (f * f).sum(); done += m
c = p * math.tan(math.pi / p); E = tot / done; se = c * math.sqrt(tot2 / done - E * E) / math.sqrt(done)
extra = 8 / (3 * p * p) if p % 2 == 0 else 0.0
print(f"p={p} nondegenerate={c*E:.5f} degenerate={extra:.5f} total={c*E+extra:.5f} +- {se:.5f}")
