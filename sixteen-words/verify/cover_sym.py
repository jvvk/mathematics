"""Symmetric deletion covers for larger n (MO q/142857), memory-light version of cover.py --sym.

S is forced closed under complement and reversal, so one Boolean per orbit of (n-b)-bit words,
and (since S is symmetric) one clause per orbit of n-bit words suffices.

Usage: python cover_sym.py N B [--bound K] [--secs T] [--hint FILE]
Prints each improving solution as it is found, verified against the full coverage table.
"""

import argparse
import time

import numpy as np
from ortools.sat.python import cp_model


def rev(y: int, m: int) -> int:
    return int(format(y, f"0{m}b")[::-1], 2)


def orbit_rep(m: int) -> np.ndarray:
    full = (1 << m) - 1
    return np.array(
        [min(y, y ^ full, rev(y, m), rev(y, m) ^ full) for y in range(1 << m)],
        dtype=np.int64,
    )


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("n", type=int)
    ap.add_argument("b", type=int)
    ap.add_argument("--bound", type=int, default=0)
    ap.add_argument("--secs", type=float, default=600.0)
    a = ap.parse_args()
    n, m = a.n, a.n - a.b
    t0 = time.time()
    yrep = orbit_rep(m)
    reps = np.unique(yrep)
    ridx = {int(r): i for i, r in enumerate(reps)}
    xrep = orbit_rep(n)
    xs_keep = np.unique(xrep)  # one n-bit word per orbit
    xs = np.arange(1 << n, dtype=np.int64)
    xbits = [((xs >> j) & 1).astype(np.int8) for j in range(n)]
    # cov[i, k]: orbit i of short words covers the k-th kept long word
    cov = np.zeros((len(reps), len(xs_keep)), dtype=bool)
    for y in range(1 << m):
        ybits = np.array([(y >> j) & 1 for j in range(m)] + [2], dtype=np.int8)
        p = np.zeros(1 << n, dtype=np.int8)
        for j in range(n):
            p += (xbits[j] == ybits[p]).astype(np.int8)
        cov[ridx[int(yrep[y])]] |= (p == m)[xs_keep]
    del xbits
    weight = np.array([(yrep == r).sum() for r in reps])
    print(
        f"n={n} b={a.b} orbits(short)={len(reps)} orbits(long)={len(xs_keep)} table {time.time() - t0:.0f}s",
        flush=True,
    )

    model = cp_model.CpModel()
    var = [model.NewBoolVar(f"o{i}") for i in range(len(reps))]
    seen: set[bytes] = set()
    for k in range(len(xs_keep)):
        col = cov[:, k]
        key = np.packbits(col).tobytes()
        if key not in seen:
            seen.add(key)
            model.AddBoolOr([var[i] for i in np.nonzero(col)[0]])
    size = sum(int(weight[i]) * var[i] for i in range(len(reps)))
    if a.bound:
        model.Add(size <= a.bound)
    model.Minimize(size)
    print(f"clauses={len(seen)} built {time.time() - t0:.0f}s", flush=True)

    class Log(cp_model.CpSolverSolutionCallback):
        def on_solution_callback(self) -> None:
            chosen = [i for i in range(len(reps)) if self.Value(var[i])]
            ok = bool(cov[chosen].any(axis=0).all())
            S = sorted(
                format(int(y), f"0{m}b")[::-1]
                for y in range(1 << m)
                if ridx[int(yrep[y])] in set(chosen)
            )
            print(
                f"[{time.time() - t0:.0f}s] |S|={len(S)} verified={ok} bound={self.BestObjectiveBound()}",
                flush=True,
            )
            print("  " + " ".join(S), flush=True)

    solver = cp_model.CpSolver()
    solver.parameters.num_workers = 1
    solver.parameters.max_time_in_seconds = a.secs
    st = solver.Solve(model, Log())
    print(
        f"status={solver.StatusName(st)} best={solver.ObjectiveValue() if st in (2, 4) else None} bound={solver.BestObjectiveBound()}"
    )


if __name__ == "__main__":
    main()
