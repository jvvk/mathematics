"""Glue layouts for the pentagonal inflation step, via CP-SAT AddCircuit (single worker).

Sums: odd generalized pentagonal numbers. f_c(v) = 49v + (c if v odd else 2 - c); 49 P_k + 2 = P_(7k-1).
Offsets c in [-23, 25] (pairs c <-> 2 - c, fixed c = 1); glue 1..25; N = 49n + r, r in [26, 74], p = n % 2.
Block c uses t (length n+1) iff its top offset o_c = (c if n+1 odd else 2 - c) is <= r - 49.
Chains run from A = 1 to B[len % 2]."""
from __future__ import annotations
import json, sys
from math import isqrt
from ortools.sat.python import cp_model

LO, HI, SHIFT, GLUE = -23, 25, 2, 25


def is_gpent(s: int) -> bool:
    d = 24 * s + 1
    r = isqrt(d)
    return s >= 0 and r * r == d and r % 6 in (1, 5)


def opent(s: int) -> bool:
    return s % 2 == 1 and is_gpent(s)


def f(c: int, v: int) -> int:
    return 49 * v + (c if v % 2 else SHIFT - c)


def blocks_for(r: int, p: int) -> list[tuple[int, str]]:
    K = r - 49
    out = []
    for c in range(LO, HI + 1):
        o = c if (p + 1) % 2 == 1 else SHIFT - c
        out.append((c, "t" if o <= K else "s"))
    return out


def solve(r: int, p: int, A: int, B: dict[int, int], time_limit: float = 30.0):
    end = B[(p + r) % 2]
    blks = blocks_for(r, p)
    ends = {}
    for c, w in blks:
        lp = p if w == "s" else 1 - p
        ends[(c, w)] = (f(c, A), f(c, B[lp]))
    nodes = [("g", g) for g in range(1, GLUE + 1)] + [("e", bk, i) for bk in blks for i in (0, 1)]
    val = lambda q: q[1] if q[0] == "g" else ends[q[1]][q[2]]
    idx = {q: i for i, q in enumerate(nodes)}
    D = len(nodes)
    m = cp_model.CpModel(); arcs, lit = [], {}

    def add(i, j):
        v = m.NewBoolVar(""); lit[(i, j)] = v; arcs.append((i, j, v))

    for q in nodes:
        for w in nodes:
            if q != w and ((q[0] == "e" and w[0] == "e" and q[1] == w[1]) or opent(val(q) + val(w))):
                add(idx[q], idx[w])
    add(idx[("g", end)], D); add(D, idx[("g", A)])
    m.Add(lit[(idx[("g", end)], D)] == 1); m.Add(lit[(D, idx[("g", A)])] == 1)
    for bk in blks:
        i, j = idx[("e", bk, 0)], idx[("e", bk, 1)]
        m.Add(lit[(i, j)] + lit[(j, i)] == 1)
    m.AddCircuit(arcs)
    s = cp_model.CpSolver(); s.parameters.num_workers = 1; s.parameters.max_time_in_seconds = time_limit
    st = s.Solve(m)
    if st not in (cp_model.OPTIMAL, cp_model.FEASIBLE):
        return None
    succ = {i: j for (i, j, v) in arcs if s.Value(v)}
    order, cur = [], idx[("g", A)]
    while cur != D:
        order.append(nodes[cur]); cur = succ[cur]
    items, k = [], 0
    while k < len(order):
        q = order[k]
        if q[0] == "g":
            items.append(("g", q[1])); k += 1
        else:
            items.append(("b", q[1], q[2] == 1)); k += 2
    return items


if __name__ == "__main__":
    A = int(sys.argv[3]) if len(sys.argv) > 3 else 1; B = {0: int(sys.argv[1]), 1: int(sys.argv[2])}
    res, bad = {}, []
    for p in (0, 1):
        for r in range(26, 75):
            it = solve(r, p, A, B)
            res[f"{r},{p}"] = it
            if it is None:
                bad.append((r, p))
    print("B =", B, "failed:", len(bad), bad[:20])
    if not bad:
        json.dump({"A": A, "B": B, "layouts": res}, open("../verify/layouts.json", "w"))
        print("saved verify/layouts.json")
    sys.exit(1 if bad else 0)
