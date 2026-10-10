"""Check the parametric representation  p_m = (1/pi) int_{Delta_5} prod_e beta_e^(1/2) / Phi(beta)^2  (K4)
and its 2D analogue for the triangle (must give 1/4)."""
import itertools, sys
import numpy as np

# K4 edges on vertices 0..3; Phi = sum over spanning trees T of prod_{e not in T} beta_e
E = list(itertools.combinations(range(4), 2))
def is_tree(es):
    parent = list(range(4))
    def find(x):
        while parent[x] != x: x = parent[x]
        return x
    for e in es:
        u, v = find(E[e][0]), find(E[e][1])
        if u == v: return False
        parent[u] = v
    return True
TREES = [t for t in itertools.combinations(range(6), 3) if is_tree(t)]
assert len(TREES) == 16
COTREES = [tuple(e for e in range(6) if e not in t) for t in TREES]

def Phi(b):  # b: (N, 6)
    return sum(np.prod(b[:, list(c)], axis=1) for c in COTREES)

def mc(N, seed):
    rng = np.random.default_rng(seed)
    tot = []
    for _ in range(N // 10**6):
        b = rng.dirichlet(np.ones(6), size=10**6)
        # Dirichlet(1^6) has density 5! on the simplex; the simplex has volume 1/5!
        f = np.prod(np.sqrt(b), axis=1) / Phi(b) ** 2 / 120.0
        tot.append(f)
    f = np.concatenate(tot)
    return 8 * f.mean() / np.pi, 8 * f.std() / np.pi / np.sqrt(len(f))

if __name__ == "__main__":
    print("K4:", *mc(int(float(sys.argv[1])), 1), " target 0.01257499441")
