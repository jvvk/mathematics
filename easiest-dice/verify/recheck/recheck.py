"""Independent recheck for "Capped dice" (MSE 5149864). Shares no code with ../check.py or the Lean files.

Searches for the smallest overlap sum_w min(P(w), Q(w)) over capped pairs (p, q), rolled n times, by random restarts
and projected local moves in floating point, and compares it with the staircase value computed by an independent
formula (sort the likelihood ratios; overlap = sum over words of min). A search can only find upper bounds on the
minimum, so a value below the staircase would refute the theorem; values close to it show the search is not blind.

    timeout 900 nice -n 15 ~/.venvs/main/bin/python recheck.py
"""

from __future__ import annotations

import itertools
import sys

import numpy as np

rng = np.random.default_rng(5149864)


def project(x: np.ndarray, cap: float) -> np.ndarray:
    """Euclidean projection onto {0 <= x_i <= cap, sum x = 1} by bisection on the shift."""
    lo, hi = x.min() - cap, x.max()
    for _ in range(80):
        mid = (lo + hi) / 2
        if np.clip(x - mid, 0, cap).sum() > 1:
            lo = mid
        else:
            hi = mid
    return np.clip(x - hi, 0, cap)


def overlap(p: np.ndarray, q: np.ndarray, n: int) -> float:
    P, Q = np.ones(1), np.ones(1)
    for _ in range(n):
        P, Q = np.outer(P, p).ravel(), np.outer(Q, q).ravel()
    return float(np.minimum(P, Q).sum())


def staircase(k: int, r: float) -> tuple[np.ndarray, np.ndarray]:
    p = np.array([min(r, max(0.0, 1 - i * r)) for i in range(k)])
    return p, p[::-1].copy()


def search(k: int, r: float, n: int, cap: float, restarts: int = 30, steps: int = 400) -> float:
    best = np.inf
    for _ in range(restarts):
        p = project(rng.random(k), cap)
        q = project(rng.random(k), cap)
        cur = overlap(p, q, n)
        step = 0.2
        for _ in range(steps):
            p2 = project(p + step * rng.normal(size=k), cap)
            q2 = project(q + step * rng.normal(size=k), cap)
            v = overlap(p2, q2, n)
            if v < cur:
                p, q, cur = p2, q2, v
            else:
                step *= 0.995
        best = min(best, cur)
    return best


def run(cap_factor: float = 1.0) -> list[str]:
    bad = []
    for k, r, n in [(4, 0.4, 2), (4, 0.4, 3), (4, 0.36, 4), (4, 0.45, 3), (3, 0.4, 2), (5, 0.3, 2), (5, 0.45, 2),
                    (6, 0.27, 2), (4, 0.3, 3)]:
        star = overlap(*staircase(k, r), n)
        found = search(k, r, n, cap=min(1.0, r * cap_factor))
        print(f"k={k} r={r} n={n}: staircase {star:.6f}, search min {found:.6f}", flush=True)
        if found < star - 1e-9:
            bad.append(f"k={k} r={r} n={n}: {found} < {star}")
        if found > star + 2e-3:
            bad.append(f"k={k} r={r} n={n}: search blind ({found} vs {star})")
    return bad


if __name__ == "__main__":
    bad = run()
    if bad:
        sys.exit("FAIL: " + "; ".join(bad))
    print("positive run: no capped pair beats the staircase; the search reaches it\n", flush=True)
    mutant = run(cap_factor=1.25)  # mutant: cap relaxed to 1.25 r, the staircase must lose
    if not any("<" in b for b in mutant):
        sys.exit("UNDETECTED MUTANT: relaxed cap")
    print("rejected mutant: relaxed cap (the search beats the staircase)")
