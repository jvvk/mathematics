"""High-precision check of  p_m = (8/pi) int_{Delta_5} prod_e beta_e^(1/2) / U(beta)^2 dsigma  (U = Symanzik of K4).

Projective form: the simplex integral of g (degree -3) equals the chart integral of g/(sum beta)^3 (degree -6).
Primary sectors (beta_k largest, beta_j = t_j beta_k) give six cube integrals; t = s^2 removes the square roots,
leaving a bounded integrand on [0,1]^5. Usage: feynman_hp.py ORDER [SECTOR|all]."""
import itertools, sys
import numpy as np

E = list(itertools.combinations(range(4), 2))

def _is_tree(es: tuple[int, ...]) -> bool:
    parent = list(range(4))
    def find(x: int) -> int:
        while parent[x] != x:
            x = parent[x]
        return x
    for e in es:
        u, v = find(E[e][0]), find(E[e][1])
        if u == v:
            return False
        parent[u] = v
    return True

TREES = [t for t in itertools.combinations(range(6), 3) if _is_tree(t)]
assert len(TREES) == 16
COTREES = [[e for e in range(6) if e not in t] for t in TREES]

def U(b: np.ndarray) -> np.ndarray:
    return sum(np.prod(b[:, c], axis=1) for c in COTREES)

def sector(k: int, order: int, chunk: int = 400_000) -> float:
    x, w = np.polynomial.legendre.leggauss(order)
    x, w = (x + 1) / 2, w / 2
    others = [j for j in range(6) if j != k]
    grid = np.array(list(itertools.product(range(order), repeat=5)), dtype=np.int32)
    tot = 0.0
    for i in range(0, len(grid), chunk):
        g = grid[i:i + chunk]
        s = x[g]                                   # (N, 5)
        wt = np.prod(w[g], axis=1)
        b = np.ones((len(g), 6))
        b[:, others] = s * s
        # dt_j = 2 s_j ds_j, t_j^(1/2) = s_j  ->  2 s_j^2 per variable; beta_k^(1/2) = 1
        f = 32 * np.prod(s * s, axis=1) / (U(b) ** 2 * b.sum(axis=1) ** 3)
        tot += float(wt @ f)
    return tot

if __name__ == "__main__":
    order = int(sys.argv[1])
    which = sys.argv[2] if len(sys.argv) > 2 else "0"
    if which == "all":
        vals = [sector(k, order) for k in range(6)]
        print("sectors:", " ".join(f"{v:.12f}" for v in vals))
        I = sum(vals)
    else:
        I = 6 * sector(int(which), order)
    print(f"order {order}: p_m = {8 * I / np.pi:.13f}   target 0.01257499441(65)")
