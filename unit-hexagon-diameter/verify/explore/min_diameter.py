"""Numerical minimum diameter of simple unit n-gons (evidence only, not a proof).

Usage: python min_diameter.py n starts
Minimises the squared diameter over edge directions, subject to closure and a minimum
separation delta between nonadjacent edges, for several delta. Prints the best diameter found.
"""
import itertools
import math
import sys

import numpy as np
from scipy.optimize import minimize


def verts(phi):
    v = np.stack([np.cos(phi), np.sin(phi)], axis=1)
    return np.vstack([np.zeros(2), np.cumsum(v, axis=0)])[: len(phi)]


def seg_dist(p, q, r, s):
    def orient(a, b, c):
        return (b[0] - a[0]) * (c[1] - a[1]) - (b[1] - a[1]) * (c[0] - a[0])
    if orient(p, q, r) * orient(p, q, s) <= 0 and orient(r, s, p) * orient(r, s, q) <= 0:
        return 0.0
    def pt(x, a, b):
        d = b - a
        t = np.clip(np.dot(x - a, d) / np.dot(d, d), 0, 1)
        return np.linalg.norm(x - (a + t * d))
    return min(pt(p, r, s), pt(q, r, s), pt(r, p, q), pt(s, p, q))


def separation(V):
    n = len(V)
    return min(seg_dist(V[i], V[(i + 1) % n], V[j], V[(j + 1) % n])
               for i in range(n) for j in range(i + 2, n) if not (i == 0 and j == n - 1))


def main():
    n, starts = int(sys.argv[1]), int(sys.argv[2])
    rng = np.random.default_rng(n)
    for delta in (0.02, 0.005):
        best = (math.inf, None)
        for _ in range(starts):
            x0 = np.append(rng.uniform(0, 2 * np.pi, n), 4.0)
            cons = [{"type": "eq", "fun": lambda x: np.sum(np.cos(x[:n]))},
                    {"type": "eq", "fun": lambda x: np.sum(np.sin(x[:n]))},
                    {"type": "ineq", "fun": lambda x: separation(verts(x[:n])) - delta}]
            for i, j in itertools.combinations(range(n), 2):
                cons.append({"type": "ineq",
                             "fun": lambda x, i=i, j=j: x[n] - np.sum((verts(x[:n])[i] - verts(x[:n])[j]) ** 2)})
            res = minimize(lambda x: x[n], x0, constraints=cons, method="SLSQP",
                           options={"maxiter": 500, "ftol": 1e-12})
            phi = res.x[:n]
            if abs(np.sum(np.cos(phi))) + abs(np.sum(np.sin(phi))) > 1e-8:
                continue
            V = verts(phi)
            if separation(V) < delta / 2:
                continue
            d = max(np.linalg.norm(V[i] - V[j]) for i in range(n) for j in range(i))
            if d < best[0]:
                best = (d, V)
        print(f"n={n} delta={delta}: smallest diameter {best[0]:.6f} (sqrt2 = {math.sqrt(2):.6f})")
        if best[1] is not None:
            print(np.round(best[1], 4).tolist())


if __name__ == "__main__":
    main()
