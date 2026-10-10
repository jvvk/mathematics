"""Relative weights (Conway soldiers: weight depends on offset from the piece): lose decided by
sum_{c in reach} w[c - pos] + g[pos], over GF(2) and as a real threshold (LP)."""
import csv

import numpy as np
from scipy.optimize import linprog

SIDE = 7
OFF = 2 * SIDE - 1                     # offsets -(SIDE-1)..(SIDE-1) in each coordinate
NREL, NPOS = OFF * OFF, SIDE * SIDE
NVAR = NREL + NPOS

rows = {}
for r in csv.DictReader(open("w7big.csv")):
    if int(r["outdeg"]) == 0:
        continue
    rows[(int(r["x"]), int(r["y"]), r["reachbits"])] = int(r["lose"])
print(len(rows), "distinct positions")


def vec(x: int, y: int, bits: str) -> list[int]:
    idx = []
    for c, b in enumerate(bits):
        if b == "1":
            dx, dy = c % SIDE - x, c // SIDE - y
            idx.append((dy + SIDE - 1) * OFF + dx + SIDE - 1)
    idx.append(NREL + y * SIDE + x)
    return idx


basis, ok = {}, True
for (x, y, bits), v in rows.items():
    mask = 0
    for i in vec(x, y, bits):
        mask ^= 1 << i
    rhs = v
    while mask:
        p = mask.bit_length() - 1
        if p not in basis:
            basis[p] = (mask, rhs)
            break
        mask ^= basis[p][0]
        rhs ^= basis[p][1]
    else:
        if rhs:
            ok = False
            break
print("GF(2) relative weighting exists:", ok, "(rank", len(basis), ")")

a_ub = []
for (x, y, bits), v in rows.items():
    row = np.zeros(NVAR)
    for i in vec(x, y, bits):
        row[i] += 1.0
    a_ub.append(-row if v else row)
res = linprog(np.zeros(NVAR), A_ub=np.array(a_ub), b_ub=-np.ones(len(a_ub)),
              bounds=[(None, None)] * NVAR, method="highs")
print("real threshold relative weighting exists:", res.status == 0)
