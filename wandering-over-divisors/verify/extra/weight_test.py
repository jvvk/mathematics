"""Is there a weight per square that decides the game? Exact feasibility tests on oracle-labelled positions.

GF(2): lose == sum_{c in reach} w[c] + g[pos] (mod 2).
Real (Conway soldiers / pagoda style): lose <=> sum_{c in reach} w[c] + g[pos] >= 1, win <=> <= -1 (LP).
Infeasible on the sample => no such weighting exists at all.
"""
import csv
import sys

import numpy as np
from scipy.optimize import linprog


def load(path: str) -> list[tuple[int, int, int, str]]:
    rows = {}
    for r in csv.DictReader(open(path)):
        if int(r["outdeg"]) == 0:
            continue
        key = (int(r["x"]), int(r["y"]), r["reachbits"])
        rows[key] = int(r["lose"])
    return [(x, y, v, bits) for (x, y, bits), v in rows.items()]


def gf2_consistent(rows: list[tuple[int, int, int, str]], ncell: int, side: int) -> tuple[bool, int]:
    nvar = 2 * ncell
    basis: dict[int, tuple[int, int]] = {}  # pivot bit -> (row mask, rhs)
    for x, y, v, bits in rows:
        mask = sum(1 << c for c, b in enumerate(bits) if b == "1") | (1 << (ncell + y * side + x))
        rhs = v
        while mask:
            p = mask.bit_length() - 1
            if p not in basis:
                basis[p] = (mask, rhs)
                break
            bm, br = basis[p]
            mask ^= bm
            rhs ^= br
        else:
            if rhs:
                return False, len(basis)
    return True, len(basis)


def lp_feasible(rows: list[tuple[int, int, int, str]], ncell: int, side: int) -> bool:
    a_ub, b_ub = [], []
    for x, y, v, bits in rows:
        row = np.zeros(2 * ncell)
        for c, b in enumerate(bits):
            if b == "1":
                row[c] = 1.0
        row[ncell + y * side + x] = 1.0
        if v:   # sum >= 1  ->  -sum <= -1
            a_ub.append(-row)
        else:   # sum <= -1
            a_ub.append(row)
        b_ub.append(-1.0)
    res = linprog(np.zeros(2 * ncell), A_ub=np.array(a_ub), b_ub=np.array(b_ub),
                  bounds=[(None, None)] * (2 * ncell), method="highs")
    return res.status == 0


for path, side in (("w5.csv", 5), ("w7.csv", 7)):
    rows = load(path)
    ncell = side * side
    ok, rank = gf2_consistent(rows, ncell, side)
    print(f"{side}x{side}: {len(rows)} distinct positions; GF(2) weighting exists: {ok} (rank reached {rank})")
    print(f"{side}x{side}: real threshold weighting exists: {lp_feasible(rows, ncell, side)}")
