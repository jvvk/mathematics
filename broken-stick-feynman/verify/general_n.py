"""The identity for every n, tested by Monte Carlo on both sides.

Left side:  p_n = P(N = n(n+1)/2 iid Exp(1) lengths on the edges of K_{n+1} are the edge lengths of an n-simplex),
            tested directly: the Gram matrix built from the squared lengths is positive definite (Schoenberg).
Right side: C_n * Gamma(N/2) * int over the unit simplex of prod_e s_e^((n-2)/2) / U(s)^((n+1)/2),
            U = first Symanzik polynomial of K_{n+1}, computed here as prod_e s_e * det L(1/s) (matrix-tree theorem),
            C_n = 2^(N-n) pi^(-N/2) Gamma_n((n+1)/2), Gamma_n the multivariate gamma function.
Usage: python3 general_n.py [samples_per_side]   (single core; default 2e7)
"""
from __future__ import annotations

import itertools
import math
import sys

import numpy as np


def edges(n: int) -> list[tuple[int, int]]:
    return list(itertools.combinations(range(n + 1), 2))


def mgamma(n: int, a: float) -> float:
    """Gamma_n(a) = pi^(n(n-1)/4) prod_{j<n} Gamma(a - j/2)."""
    return math.pi ** (n * (n - 1) / 4) * math.prod(math.gamma(a - j / 2) for j in range(n))


def C(n: int) -> float:
    N = n * (n + 1) // 2
    return 2 ** (N - n) * math.pi ** (-N / 2) * mgamma(n, (n + 1) / 2)


def direct(n: int, M: int, rng: np.random.Generator, chunk: int = 10**6) -> tuple[float, float]:
    E = edges(n)
    hits = 0
    for _ in range(M // chunk):
        l2 = rng.exponential(size=(chunk, len(E))) ** 2
        d2 = np.zeros((chunk, n + 1, n + 1))
        for k, (i, j) in enumerate(E):
            d2[:, i, j] = d2[:, j, i] = l2[:, k]
        G = 0.5 * (d2[:, 1:, :1] + d2[:, :1, 1:] - d2[:, 1:, 1:])
        hits += int(np.sum(np.linalg.eigvalsh(G)[:, 0] > 0))
    p = hits / M
    return p, math.sqrt(p * (1 - p) / M)


def symanzik(n: int, s: np.ndarray) -> np.ndarray:
    """U(s) = prod s * det(reduced Laplacian of K_{n+1} with edge weights 1/s)."""
    E = edges(n)
    L = np.zeros((len(s), n + 1, n + 1))
    for k, (i, j) in enumerate(E):
        w = 1.0 / s[:, k]
        L[:, i, i] += w
        L[:, j, j] += w
        L[:, i, j] -= w
        L[:, j, i] -= w
    return np.prod(s, axis=1) * np.linalg.det(L[:, 1:, 1:])


def parametric(n: int, M: int, rng: np.random.Generator, chunk: int = 10**6) -> tuple[float, float]:
    N = n * (n + 1) // 2
    vals = []
    for _ in range(M // chunk):
        s = rng.dirichlet(np.ones(N), size=chunk)  # density (N-1)! on the simplex
        f = np.prod(s ** ((n - 2) / 2), axis=1) / symanzik(n, s) ** ((n + 1) / 2) / math.factorial(N - 1)
        vals.append(f)
    f = np.concatenate(vals) * C(n) * math.gamma(N / 2)
    return float(f.mean()), float(f.std() / math.sqrt(len(f)))


if __name__ == "__main__":
    M = int(float(sys.argv[1])) if len(sys.argv) > 1 else 2 * 10**7
    rng = np.random.default_rng(142983)
    assert abs(C(2) - 1 / math.sqrt(math.pi)) < 1e-15 and abs(C(3) - 4 / math.pi) < 1e-15
    for n in range(2, 8):  # the positions route gives 2^(N-n) Gamma((n+1)/2) Gamma_n(n/2) pi^(-(N+1)/2): same constant
        N = n * (n + 1) // 2
        alt = 2 ** (N - n) * math.gamma((n + 1) / 2) * mgamma(n, n / 2) * math.pi ** (-(N + 1) / 2)
        assert abs(C(n) / alt - 1) < 1e-12, n
    for n in (2, 3, 4):
        a, sa = direct(n, M, rng)
        b, sb = parametric(n, M, rng)
        z = abs(a - b) / math.hypot(sa, sb)
        print(f"n={n}: direct {a:.6g} +- {sa:.2g}   parametric {b:.6g} +- {sb:.2g}   ({z:.1f} se)", flush=True)
        assert z < 4, (n, z)
    print("identity agrees for n = 2, 3, 4")
