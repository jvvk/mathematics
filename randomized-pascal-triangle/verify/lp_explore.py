"""Exploratory LP search for drift potentials of window width m+1 (NOT a proof; certify separately).

Potential F(x) = sum_j f(x_j..x_{j+m}), f a combination of homogeneous piecewise-linear features.
Local drift on the input window X_0..X_{m+1} = x_{j-1}..x_{j+m}, outputs Y_i = T(X_i, X_{i+1}), i = 0..m:
    G = E f(Y) - lam f(X_1..X_{m+1}) + [psi(X_1..X_{m+1}) - psi(X_0..X_m)] + E[chi(Y_1..Y_m) - chi(Y_0..Y_{m-1})]
The brackets telescope over j. Need G >= 0 at all nonnegative X, and F(x0) > 0 for x0 = [1].
Since every feature is bounded by a multiple of S, signs of the coefficients of f are unrestricted.

Usage: python lp_explore.py M [p values...]
"""

from __future__ import annotations

import itertools
import sys

import numpy as np
from scipy.optimize import linprog


def feats(Z: np.ndarray) -> tuple[list[str], np.ndarray]:
    """Features of rows Z (N x w)."""
    N, w = Z.shape
    names, cols = [], []

    def add(n, c):
        names.append(n)
        cols.append(c)

    for i in range(w):
        add(f"z{i}", Z[:, i])
    for i, k in itertools.combinations(range(w), 2):
        add(f"|z{i}-z{k}|", np.abs(Z[:, i] - Z[:, k]))
    for i in range(w - 2):
        a, b, c = Z[:, i], Z[:, i + 1], Z[:, i + 2]
        add(f"W{i}", np.abs(np.abs(a - b) - np.abs(b - c)))
        add(f"D2_{i}", np.abs(a - 2 * b + c))
        add(f"max3_{i}", np.maximum(np.maximum(a, b), c))
        add(f"min3_{i}", np.minimum(np.minimum(a, b), c))
    for i in range(w - 3):
        a, b, c, d = (Z[:, i + k] for k in range(4))
        add(f"W2_{i}", np.abs(np.abs(a - c) - np.abs(b - d)))
        add(
            f"WW_{i}",
            np.abs(
                np.abs(np.abs(a - b) - np.abs(b - c))
                - np.abs(np.abs(b - c) - np.abs(c - d))
            ),
        )
    return names, np.stack(cols, axis=1)


def system(X: np.ndarray, p: float, lam: float, m: int):
    """Columns: [f features | psi features | chi features]; rows: points."""
    N = len(X)
    nf, fin = feats(X[:, 1:])
    out = np.zeros_like(fin)
    nc, _ = feats(X[:, :m]) if m >= 1 else ([], None)
    chi = None
    for bits in itertools.product([0, 1], repeat=m + 1):
        wgt = np.prod([p if b else 1 - p for b in bits])
        Y = np.stack(
            [
                X[:, i] + X[:, i + 1] if bits[i] else np.abs(X[:, i] - X[:, i + 1])
                for i in range(m + 1)
            ],
            1,
        )
        out += wgt * feats(Y)[1]
        if m >= 1:
            c = feats(Y[:, 1:])[1] - feats(Y[:, :-1])[1]
            chi = wgt * c if chi is None else chi + wgt * c
    psi = feats(X[:, 1:])[1] - feats(X[:, :-1])[1]
    cols = [out - lam * fin, psi] + ([chi] if chi is not None else [])
    return nf, np.concatenate(cols, axis=1)


def x0_values(m: int) -> np.ndarray:
    """F(x0) per f-feature: sum over all windows of the zero-padded row [1]."""
    w = m + 1
    row = np.zeros(2 * w + 1)
    row[w] = 1
    Z = np.stack([row[j : j + w] for j in range(len(row) - w + 1)])
    return feats(Z)[1].sum(axis=0)


def points(m: int, K: int, nrand: int, seed: int = 0) -> np.ndarray:
    w = m + 2
    grid = np.array(list(itertools.product(range(K + 1), repeat=w)), dtype=float)
    grid = grid[grid.sum(1) > 0]
    rng = np.random.default_rng(seed)
    r = np.exp(rng.uniform(-4, 4, (nrand, w))) * (rng.random((nrand, w)) > 0.25)
    r = r[r.sum(1) > 0]
    return np.concatenate([grid, r])


def feasible(X, p, lam, m, bound=50.0):
    nf, A = system(X, p, lam, m)
    nvar = A.shape[1]
    x0 = np.zeros(nvar)
    x0[: len(nf)] = x0_values(m)
    # A v >= 0 for all points; F(x0) = 1
    res = linprog(
        np.zeros(nvar),
        A_ub=-A,
        b_ub=np.zeros(len(A)),
        A_eq=x0[None, :],
        b_eq=[1.0],
        bounds=[(-bound, bound)] * nvar,
        method="highs",
    )
    return res.status == 0, res, nf


def threshold(m, K, nrand, lam=1.0001, lo=0.0, hi=0.4, tol=2e-3):
    X = points(m, K, nrand)
    while hi - lo > tol:
        mid = (lo + hi) / 2
        ok = feasible(X, mid, lam, m)[0]
        print(f"  m={m} p={mid:.4f} {'feasible' if ok else 'infeasible'}", flush=True)
        lo, hi = (lo, mid) if ok else (mid, hi)
    return hi


if __name__ == "__main__":
    m = int(sys.argv[1])
    K = {1: 8, 2: 6, 3: 4, 4: 3}[m]
    print(f"m={m}: cutoff <= {threshold(m, K, 4000):.4f} (sampled; not certified)")
