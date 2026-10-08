"""Which structural candidates survive the linear necessary conditions? (exploration, MO 442949)

Variables: sorted turns A_0 < ... < A_{n-2} (positive) and the resultant direction phi.
For a normalized candidate (p, q) with p_0 = 0, every global optimum satisfies (strict, homogeneous, linear):
  * length exchange, positions i < j:  l_i > l_j  =>  theta_i + theta_j > 2 phi,  l_i < l_j  =>  < 2 phi
  * adjacent turn exchange: (a_i - a_{i+1}) (theta_i + theta_{i+2} - 2 phi) < 0
  * endpoint move (Lemma 2.3): 2 phi < T + a_0
Homogeneous strict system: feasible iff the LP with margin >= 1 is feasible (scale).
Usage: python lp_exclude.py N_MAX
"""

from __future__ import annotations

import itertools
import sys

import numpy as np
from scipy.optimize import linprog


def candidates(n: int):
    """Normalized structural candidates: p = (0, S up, n-1, S^c down, 1), q a valley with first descent and
    (n >= 4) last ascent."""
    mid = list(range(2, n - 1))
    ps = []
    for r in range(len(mid) + 1):
        for S in itertools.combinations(mid, r):
            rest = sorted(set(mid) - set(S), reverse=True)
            ps.append((0, *S, n - 1, *rest, 1))
    qs = []
    for perm in itertools.permutations(range(n - 1)):
        k = perm.index(0)
        if all(perm[i] > perm[i + 1] for i in range(k)) and all(
            perm[i] < perm[i + 1] for i in range(k, n - 2)
        ):
            if n >= 3 and not (perm[0] > perm[1]):
                continue
            if n >= 4 and not (perm[-2] < perm[-1]):
                continue
            qs.append(perm)
    return [(p, q) for p in ps for q in qs]


def rows(n: int, p, q):
    """Inequalities as coefficient rows c with c . (A_0..A_{n-2}, phi) > 0."""
    m = n - 1
    theta = [np.zeros(m + 1)]
    for i in range(m):
        v = theta[-1].copy()
        v[q[i]] += 1
        theta.append(v)
    phi = np.zeros(m + 1)
    phi[m] = 1
    R = []
    R.append(np.eye(m + 1)[0])  # A_0 > 0
    for k in range(m - 1):  # A_{k+1} > A_k
        R.append(np.eye(m + 1)[k + 1] - np.eye(m + 1)[k])
    for i, j in itertools.combinations(range(n), 2):  # length exchange
        s = theta[i] + theta[j] - 2 * phi
        R.append(s if p[i] > p[j] else -s)
    for i in range(n - 2):  # turn exchange
        s = theta[i] + theta[i + 2] - 2 * phi
        R.append(-s if q[i] > q[i + 1] else s)
    a0 = np.eye(m + 1)[q[0]]
    R.append(theta[n - 1] + a0 - 2 * phi)  # endpoint: T + a_0 - 2 phi > 0
    return np.array(R)


def feasible(n: int, p, q) -> bool:
    R = rows(n, p, q)
    res = linprog(
        np.zeros(R.shape[1]),
        A_ub=-R,
        b_ub=-np.ones(len(R)),
        bounds=[(None, None)] * R.shape[1],
        method="highs",
    )
    return res.status == 0


def family(n: int):
    """The recursive family C_n of the Codex manuscript (normalized p_0 = 0)."""
    if n == 1:
        return {((0,), ())}
    if n == 2:
        return {((0, 1), (0,))}
    if n == 3:
        return {((0, 2, 1), (1, 0))}
    out = set()
    for k in range(2, n):
        m = n - k + 1
        for P, Q in family(m):
            p = (0, *[x + (k - 1) for x in reversed(P)], *range(k - 2, 0, -1))
            qq = (n - 2, *reversed(Q), *range(n - k, n - 2))
            out.add((p, qq))
    for P, Q in family(n - 2):
        out.add(((0, *[x + 2 for x in P], 1), (n - 3, *Q, n - 2)))
    return out


if __name__ == "__main__":
    for n in range(4, int(sys.argv[1]) + 1):
        C = candidates(n)
        surv = {c for c in C if feasible(n, *c)}
        F = family(n)
        print(
            f"n={n}: candidates {len(C)}, LP survivors {len(surv)}, family {len(F)}, family subset of survivors:"
            f" {F <= surv}, extra survivors {len(surv - F)}",
            flush=True,
        )
        for c in sorted(surv - F)[:6]:
            print("   extra:", c)
