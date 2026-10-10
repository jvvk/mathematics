"""Independent recheck of the numbers in note.tex. Shares no code with verify/*.py.

Own realisability test (Sylvester's criterion on the Gram matrix), own spanning-tree enumeration (rank of the
incidence vectors over GF(2)), constants with mpmath. Checks:
  T1  p_3 by direct Monte Carlo: agrees with 0.0125749944167 and excludes 1/79
  T2  Theorem 1 for n = 3: Monte Carlo of the simplex form (7) with U from enumerated spanning trees
  T3  constants: C_2 = 1/sqrt(pi), C_3 = 4/pi, C_3 Gamma(3/2)^6 = pi^2/16, T_2 = sqrt(pi)/4, p_2 = 1/4
  T4  Zare's polytope: the 12 triangle inequalities hold with probability 1/54; 54 p_3 = 0.68
  T5  p_4 = 1.0584e-4 from the simplex form with the 125 spanning trees of K_5
  T6  the unordered probability 0.0652818 by Monte Carlo over all 720 orders
  M   three mutants of this file must each break a check
Usage: python3 recheck.py [--quick]
"""
from __future__ import annotations

import itertools
import math
import sys

import mpmath as mp
import numpy as np
from scipy import integrate

QUICK = "--quick" in sys.argv
mp.mp.dps = 40
P3, PU, P4 = 0.0125749944167, 0.0652818, 1.0584e-4
FLAGS = dict(no_volume=False, cycles_as_trees=False, wrong_gamma=False)


def realisable(L: np.ndarray, n: int, pairs: list[tuple[int, int]]) -> np.ndarray:
    """L: (M, N) lengths on the edges `pairs` of K_{n+1}. Sylvester: all leading principal minors of G > 0."""
    q = {e: L[:, k] ** 2 for k, e in enumerate(pairs)}
    d2 = lambda i, j: 0.0 if i == j else q[(min(i, j), max(i, j))]
    G = np.empty((L.shape[0], n, n))
    for i in range(1, n + 1):
        for j in range(1, n + 1):
            G[:, i - 1, j - 1] = 0.5 * (d2(0, i) + d2(0, j) - d2(i, j))
    ok = np.ones(L.shape[0], bool)
    for k in range(1, n + 1):
        if FLAGS["no_volume"] and k == n:
            continue
        ok &= np.linalg.det(G[:, :k, :k]) > 0
    if FLAGS["no_volume"]:  # mutant: faces only
        for tri in itertools.combinations(range(n + 1), 3):
            a, b, c = (L[:, pairs.index(e)] for e in itertools.combinations(tri, 2))
            ok &= (a < b + c) & (b < a + c) & (c < a + b)
    return ok


def trees(n: int) -> list[tuple[int, ...]]:
    """Spanning trees of K_{n+1}: n-edge sets whose incidence vectors are independent over GF(2)."""
    pairs = list(itertools.combinations(range(n + 1), 2))
    out = []
    for S in itertools.combinations(range(len(pairs)), n):
        rows = [(1 << pairs[e][0]) | (1 << pairs[e][1]) for e in S]
        basis: list[int] = []
        for r in rows:
            for b in basis:
                r = min(r, r ^ b)
            if r:
                basis.append(r)
        if len(basis) == n or FLAGS["cycles_as_trees"]:
            out.append(S)
    return out


def U_from_trees(n: int, s: np.ndarray) -> np.ndarray:
    N = s.shape[1]
    tot = np.zeros(len(s))
    for T in trees(n):
        omitted = [e for e in range(N) if e not in T]
        tot += np.prod(s[:, omitted], axis=1)
    return tot


def C(n: int) -> mp.mpf:
    N = n * (n + 1) // 2
    a = mp.mpf(n + 1) / 2 if not FLAGS["wrong_gamma"] else mp.mpf(n) / 2
    gam = mp.pi ** (mp.mpf(n * (n - 1)) / 4) * mp.fprod(mp.gamma(a - mp.mpf(j) / 2) for j in range(n))
    return 2 ** (N - n) * mp.pi ** (-mp.mpf(N) / 2) * gam


def simplex_form(n: int, M: int, rng: np.random.Generator) -> tuple[float, float]:
    N = n * (n + 1) // 2
    vals = []
    for _ in range(max(1, M // 500_000)):
        s = rng.dirichlet(np.ones(N), size=500_000)
        vals.append(np.prod(s, axis=1) ** ((n - 2) / 2) / U_from_trees(n, s) ** ((n + 1) / 2))
    f = np.concatenate(vals) * float(C(n) * mp.gamma(mp.mpf(N) / 2)) / math.factorial(N - 1)
    return float(f.mean()), float(f.std() / math.sqrt(len(f)))


def checks() -> list[str]:
    fails: list[str] = []

    def need(ok: bool, msg: str) -> None:
        print(("ok    " if ok else "FAIL  ") + msg)
        if not ok:
            fails.append(msg)

    rng = np.random.default_rng(20261010)
    pairs3 = list(itertools.combinations(range(4), 2))
    # T1
    M = 2 * 10**7 if QUICK else 10**8
    hits = 0
    for _ in range(M // 10**6):
        hits += int(realisable(rng.exponential(size=(10**6, 6)), 3, pairs3).sum())
    p = hits / M
    se = math.sqrt(p * (1 - p) / M)
    need(abs(p - P3) < 4 * se and (QUICK or abs(p - 1 / 79) > 4 * se),
         f"T1 direct Monte Carlo p_3 = {p:.6f} +- {se:.6f}")
    # T2
    b, sb = simplex_form(3, 10**6 if QUICK else 4 * 10**6, rng)
    need(len(trees(3)) == 16 and abs(b - P3) < 4 * sb, f"T2 simplex form p_3 = {b:.7f} +- {sb:.1e}, 16 trees")
    # T3
    T2 = integrate.quad(lambda k: 4 * math.pi * k * k / math.pi**1.5 * (k * k + 1) ** -3, 0, math.inf)[0]
    c2, c3 = C(2), C(3)
    need(abs(c2 - 1 / mp.sqrt(mp.pi)) < 1e-30 and abs(c3 - 4 / mp.pi) < 1e-30
         and abs(c3 * mp.gamma(1.5) ** 6 - mp.pi**2 / 16) < 1e-30 and abs(T2 - math.sqrt(math.pi) / 4) < 1e-10
         and abs(float(c2) * T2 - 0.25) < 1e-10 and abs(float(c2 * mp.gamma(1.5)) / 2 - 0.25) < 1e-15,
         f"T3 constants C_2 = {float(c2):.12f}, C_3 = {float(c3):.12f}, T_2 = {T2:.12f}")
    # T4
    M = 4 * 10**6 if QUICK else 2 * 10**7
    hits = 0
    for _ in range(M // 10**6):
        L = rng.exponential(size=(10**6, 6))
        ok = np.ones(10**6, bool)
        for tri in itertools.combinations(range(4), 3):
            a, bb, c = (L[:, pairs3.index(e)] for e in itertools.combinations(tri, 2))
            ok &= (a < bb + c) & (bb < a + c) & (c < a + bb)
        hits += int(ok.sum())
    z = hits / M
    sz = math.sqrt(z * (1 - z) / M)
    need(abs(z - 1 / 54) < 4 * sz and abs(54 * P3 - 0.679) < 1e-3,
         f"T4 Zare's polytope {z:.6f} +- {sz:.6f} vs 1/54 = {1/54:.6f}; 54 p_3 = {54*P3:.4f}")
    # T5
    b4, s4 = simplex_form(4, 10**6 if QUICK else 4 * 10**6, rng)
    need(len(trees(4)) == 125 and abs(b4 - P4) < 4 * s4 + 5e-9, f"T5 p_4 = {b4:.4e} +- {s4:.1e}, 125 trees")
    # T6: all 720 orders, own realisability test
    M = 2 * 10**4 if QUICK else 2 * 10**5
    L = rng.exponential(size=(M, 6))
    any_ok = np.zeros(M, bool)
    for perm in itertools.permutations(range(6)):
        any_ok |= realisable(L[:, perm], 3, pairs3)
    u = any_ok.mean()
    su = math.sqrt(u * (1 - u) / M)
    need(abs(u - PU) < 4 * su, f"T6 any order: {u:.5f} +- {su:.5f} vs 0.0652818")
    return fails


if __name__ == "__main__":
    sys.stdout.reconfigure(line_buffering=True)
    fails = checks()
    print(f"\n{'ALL CHECKS PASS' if not fails else f'{len(fails)} FAILED'}")
    QUICK = True
    killed = 0
    for key in FLAGS:
        FLAGS[key] = True
        print(f"\n--- mutant {key}")
        killed += bool(checks())
        FLAGS[key] = False
    print(f"\nmutants killed: {killed}/{len(FLAGS)}")
    sys.exit(0 if not fails and killed == len(FLAGS) else 1)
