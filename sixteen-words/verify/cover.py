"""Search for small deletion covers H(n, b) for MO q/142857.

A set S of words of length n-b covers {0,1}^n if every n-bit word has a subsequence in S.
Exact model: CP-SAT set cover, one Boolean per (n-b)-bit word, one clause per n-bit word.

Usage: python cover.py N B [--sym] [--bound K] [--secs T]
  --sym     force S closed under complement and reversal (orbit variables)
  --bound K ask for |S| <= K (feasibility) instead of minimising
"""

import argparse

import numpy as np
from ortools.sat.python import cp_model


def coverage(n: int, m: int) -> np.ndarray:
    """cov[y, x] = True iff the m-bit word y is a subsequence of the n-bit word x (bit j = position j)."""
    xs = np.arange(1 << n, dtype=np.int64)
    xbits = [((xs >> j) & 1).astype(np.int8) for j in range(n)]
    cov = np.zeros((1 << m, 1 << n), dtype=bool)
    for y in range(1 << m):
        ybits = np.array([(y >> j) & 1 for j in range(m)] + [2], dtype=np.int8)
        p = np.zeros(1 << n, dtype=np.int8)
        for j in range(n):
            p += (xbits[j] == ybits[p]).astype(np.int8)
        cov[y] = p == m
    return cov


def orbit_map(m: int) -> list[int]:
    """Representative index of each m-bit word under complement and reversal."""
    full = (1 << m) - 1

    def rev(y: int) -> int:
        return int(format(y, f"0{m}b")[::-1], 2)

    return [min(y, y ^ full, rev(y), rev(y) ^ full) for y in range(1 << m)]


def is_cover(S: list[int], n: int, m: int, cov: np.ndarray) -> bool:
    return bool(cov[S].any(axis=0).all())


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("n", type=int)
    ap.add_argument("b", type=int)
    ap.add_argument("--sym", action="store_true")
    ap.add_argument("--bound", type=int, default=0)
    ap.add_argument("--secs", type=float, default=100.0)
    a = ap.parse_args()
    n, m = a.n, a.n - a.b
    cov = coverage(n, m)
    rep = orbit_map(m) if a.sym else list(range(1 << m))
    reps = sorted(set(rep))
    model = cp_model.CpModel()
    var = {r: model.NewBoolVar(f"y{r}") for r in reps}
    weight = {r: sum(1 for y in range(1 << m) if rep[y] == r) for r in reps}
    # drop dominated x: keep one clause per distinct covering set of orbits
    seen: set[frozenset] = set()
    for x in range(1 << n):
        lits = frozenset(rep[y] for y in np.nonzero(cov[:, x])[0])
        if lits not in seen:
            seen.add(lits)
            model.AddBoolOr([var[r] for r in lits])
    size = sum(weight[r] * var[r] for r in reps)
    if a.bound:
        model.Add(size <= a.bound)
    else:
        model.Minimize(size)
    solver = cp_model.CpSolver()
    solver.parameters.num_workers = 1
    solver.parameters.max_time_in_seconds = a.secs
    st = solver.Solve(model)
    print(
        f"n={n} b={a.b} sym={a.sym} clauses={len(seen)} status={solver.StatusName(st)}"
    )
    if st in (cp_model.OPTIMAL, cp_model.FEASIBLE):
        S = [y for y in range(1 << m) if solver.Value(var[rep[y]])]
        words = sorted(format(y, f"0{m}b")[::-1] for y in S)
        print(
            f"|S|={len(S)} bound={solver.BestObjectiveBound()} verified={is_cover(S, n, m, cov)}"
        )
        print(" ".join(words))


if __name__ == "__main__":
    main()
