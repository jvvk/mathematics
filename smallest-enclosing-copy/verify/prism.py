"""Independent check of P_p = p tan(pi/p) E[Vol(T) 1{0 in T}], T = tetrahedron on 4 iid points, each on a uniformly
chosen vertical edge of the prism (regular p-gon inscribed in the unit circle) x [-1,1], height uniform.
Containment by barycentric sign test (no LP, no KKT). Mutant: centre the prism test at (0,0,0.5) instead of 0.
Odd p only: for even p, a tetrahedron with two points on one edge and one on the opposite edge has the origin exactly
on a face, and floating-point signs then decide at random; use even_p.py, which excludes these tuples by label.
Usage: prism.py p samples seed"""
import os, sys, signal, math, numpy as np
def _stop(*_): raise TimeoutError
signal.signal(signal.SIGALRM, _stop); signal.alarm(int(os.environ.get("TIME_LIMIT", "0")))
p, N, seed = map(int, sys.argv[1:4]); rng = np.random.default_rng(seed)
if p % 2 == 0: sys.exit("prism.py: odd p only (see the docstring); use even_p.py for even p")
def est(origin):
    tot = 0.0; tot2 = 0.0; done = 0
    while done < N:
        m = min(200000, N - done); a = 2 * np.pi * rng.integers(0, p, (m, 4)) / p
        X = np.stack([np.cos(a), np.sin(a), rng.uniform(-1, 1, (m, 4))], -1) - origin   # (m,4,3)
        V = np.einsum('mi,mi->m', X[:, 1] - X[:, 0], np.cross(X[:, 2] - X[:, 0], X[:, 3] - X[:, 0])) / 6
        signs = []
        for i in range(4):   # sign of the volume with vertex i replaced by the origin
            Y = X.copy(); Y[:, i] = 0
            signs.append(np.einsum('mi,mi->m', Y[:, 1] - Y[:, 0], np.cross(Y[:, 2] - Y[:, 0], Y[:, 3] - Y[:, 0])) * V > 0)
        f = np.where(np.all(signs, 0), np.abs(V), 0.0); tot += f.sum(); tot2 += (f * f).sum(); done += m
    E = tot / done; c = p * math.tan(math.pi / p); return c * E, c * math.sqrt(tot2 / done - E * E) / math.sqrt(done)
for lab, o in [("prism formula", np.zeros(3)), ("MUTANT origin (0,0,0.5)", np.array([0, 0, .5]))]:
    v, s = est(o); print(f"p={p} {lab}: {v:.5f} +- {s:.5f}")
