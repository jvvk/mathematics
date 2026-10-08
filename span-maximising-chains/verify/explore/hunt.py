"""Try to realize a given normalized pattern as the strict optimum (exploration, MO 442949).

Maximizes margin = |Z(target)|^2 - max over all other reversal classes |Z|^2, over sorted lengths and
turns with total turn < pi/2, by Nelder-Mead from random starts. Floating point: a positive margin found here
is only a lead; it must be certified exactly.
Usage: python hunt.py n "p" "q" starts
"""

from __future__ import annotations

import itertools
import sys

import numpy as np
from scipy.optimize import minimize


def all_classes(n):
    seen, out = set(), []
    for p in itertools.permutations(range(n)):
        for q in itertools.permutations(range(n - 1)):
            key = min((p, q), (p[::-1], q[::-1]))
            if key not in seen:
                seen.add(key)
                out.append(key)
    return out


def spans2(L, A, P, Q):
    th = np.concatenate([np.zeros((len(Q), 1)), np.cumsum(A[Q], axis=1)], axis=1)
    Z = (L[P] * np.exp(1j * th)).sum(axis=1)
    return np.abs(Z) ** 2


def decode(x, n):
    L = np.cumsum(np.exp(x[:n]))
    A = np.cumsum(np.exp(x[n:]))
    A = A / A[-1] * (np.pi / 2) * (1 / (1 + np.exp(-x[-1]))) / (n - 1) * 1.0
    A = np.cumsum(np.exp(x[n : 2 * n - 1]))
    s = A.sum()
    A = A / s * (np.pi / 2) * 0.999 / (1 + np.exp(-x[-1]))
    return L, A


def main():
    n = int(sys.argv[1])
    target = (tuple(int(c) for c in sys.argv[2]), tuple(int(c) for c in sys.argv[3]))
    starts = int(sys.argv[4])
    C = all_classes(n)
    P = np.array([c[0] for c in C])
    Q = np.array([c[1] for c in C])
    ti = C.index(min(target, (target[0][::-1], target[1][::-1])))
    mask = np.ones(len(C), bool)
    mask[ti] = False

    def margin(x):
        L, A = decode(x, n)
        s = spans2(L, A, P, Q) / (L.sum() ** 2)
        return s[ti] - s[mask].max()

    rng = np.random.default_rng(1)
    best = (-np.inf, None)
    for _ in range(starts):
        x0 = rng.normal(0, 1.5, 2 * n)
        r = minimize(
            lambda x: -margin(x),
            x0,
            method="Nelder-Mead",
            options=dict(maxiter=4000, xatol=1e-10, fatol=1e-14),
        )
        if -r.fun > best[0]:
            best = (-r.fun, r.x)
    L, A = decode(best[1], n)
    print(
        f"best margin {best[0]:.3e}  L={np.round(L / L[-1], 5)}  A={np.round(A, 5)}  T={A.sum():.4f}"
    )


if __name__ == "__main__":
    main()
