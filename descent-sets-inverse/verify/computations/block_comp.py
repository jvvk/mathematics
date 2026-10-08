"""Block mechanism in the composition model: alpha has r parts, delta has a part > r."""
from fractions import Fraction
from math import comb
import sys


def comps_maxpart_le(n, m):
    # number of compositions of n with all parts <= m
    c = [0] * (n + 1); c[0] = 1
    for k in range(1, n + 1):
        c[k] = sum(c[k - p] for p in range(1, min(m, k) + 1))
    return c[n]


def block(n):
    tot = 2 ** (n - 1)
    s = 0
    for r in range(1, n + 1):
        pr = comb(n - 1, r - 1)
        s += pr * (tot - comps_maxpart_le(n, r))
    return s / tot ** 2


gr = {int(l.split()[0]): float(l.split()[2]) for l in open(__import__("sys").argv[1] if len(__import__("sys").argv) > 1 else "gr_fail.txt")}
for n in sorted(gr):
    b = block(n)
    print(n, f"{gr[n]:.4e}", f"{b:.4e}", round(gr[n] / b, 4), round(gr[n] / (0.75 ** n), 3))
