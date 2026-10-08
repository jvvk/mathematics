"""Is a candidate ever the projection maximizer in its own resultant direction? (exploration, MO 442949)
Samples data near the LP-feasible region and random data; reports the best 'self-support' slack:
proj_phi(candidate) - max over all other arrangements proj_phi, with phi = arg Z(candidate).
Usage: python projopt.py n p q samples"""
import sys
import numpy as np
from scipy.optimize import minimize
from hunt import all_classes, decode

n = int(sys.argv[1]); tp = tuple(int(c) for c in sys.argv[2]); tq = tuple(int(c) for c in sys.argv[3])
C = all_classes(n); P = np.array([c[0] for c in C]); Q = np.array([c[1] for c in C])
ti = C.index(min((tp, tq), (tp[::-1], tq[::-1])))

def slack(x):
    L, A = decode(x, n)
    th = np.concatenate([np.zeros((len(Q), 1)), np.cumsum(A[Q], axis=1)], axis=1)
    Zt = (L[np.array(tp)] * np.exp(1j * np.concatenate([[0], np.cumsum(A[np.array(tq)])]))).sum()
    phi = np.angle(Zt)
    proj = (L[P] * np.cos(th - phi)).sum(axis=1)
    pt = abs(Zt)
    others = np.delete(proj, ti)
    # the reversed class has the same span but a mirrored direction; compare against all distinct displacements
    return (pt - others.max()) / L.sum()

rng = np.random.default_rng(3); best = -np.inf
for _ in range(int(sys.argv[4])):
    r = minimize(lambda x: -slack(x), rng.normal(0, 1.5, 2 * n), method="Nelder-Mead",
                 options=dict(maxiter=4000, xatol=1e-11, fatol=1e-15))
    best = max(best, -r.fun)
print("best self-support slack", best)
