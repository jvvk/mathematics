"""Literal geometric check of stage-2 tilings on a sample: place the tiles
P + l and g(P) + t + l for every lattice vector l in a box, and confirm every
cell of the window [0, W)^4 is covered exactly once. No residue arguments.
Usage: geomcheck.py cert_d5.txt s2_d5.txt SAMPLE [mutate]"""
from __future__ import annotations
import itertools, random, re, sys
import numpy as np
from verify2 import Group, parse_cells

W, TMAX = 4, 6
PAD = 9 + TMAX + 1  # tile extent + |t| + 1: every tile meeting the window is placed

def tiling_ok(line: str, cells: dict, mutate: bool) -> bool:
    uid = int(line.split()[0])
    G = Group([int(x) for x in re.search(r"group=([\dx]+)", line).group(1).split("x")])
    imgs = [tuple(map(int, c.split(","))) for c in re.findall(r"\(([\d,]+)\)", re.search(r"phi=(\S+)", line).group(1))]
    gm = re.search(r"g=perm(\d+),sign([+-]+)", line)
    perm = [int(c) for c in gm.group(1)]; sign = [1 if c == "+" else -1 for c in gm.group(2)]
    if mutate: sign[0] = -sign[0]
    P = np.array(cells[uid]); m = P.shape[1]
    gP = np.zeros_like(P)
    for j in range(m): gP[:, perm[j]] += sign[j] * P[:, j]
    A = np.array(imgs)                                   # m x k
    f = np.array(G.f)
    phi = lambda V: (V @ A) % f                          # rows -> group elements
    R = range(-PAD, W + PAD)
    box = np.array(list(itertools.product(R, repeat=m)))
    ker = box[np.all(phi(box) == 0, axis=1)]
    # t: first vector with phi(g(P)) + phi(t) disjoint from phi(P)
    target = {tuple(x) for x in phi(P)}
    for t in sorted(itertools.product(range(-TMAX, TMAX + 1), repeat=m), key=lambda v: max(map(abs, v))):
        imgsB = {tuple(x) for x in phi(gP + np.array(t))}
        if not imgsB & target: break
    else: return False
    cov = {}
    for tile in (P, gP + np.array(t)):
        for c in (tile[None, :, :] + ker[:, None, :]).reshape(-1, m):
            if np.all((c >= 0) & (c < W)):
                k = tuple(c); cov[k] = cov.get(k, 0) + 1
    return len(cov) == W ** m and all(v == 1 for v in cov.values())

cells = parse_cells(sys.argv[1]); lines = open(sys.argv[2]).read().splitlines()
random.seed(20260930); sample = random.sample(lines, int(sys.argv[3]))
mut = len(sys.argv) > 4
print(("MUTANT " if mut else "") + f"sample={len(sample)} exact_covers={sum(tiling_ok(l, cells, mut) for l in sample)}")
