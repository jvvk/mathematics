"""Glue layouts via CP-SAT AddCircuit (single worker)."""
from __future__ import annotations
from ortools.sat.python import cp_model
from layout import blocks_for, block_ends
from aligned import odd_tri


def solve(r: int, p: int, A: int, B: dict[int, int], time_limit: float = 20.0):
    end = B[(p + r) % 2]
    blks = blocks_for(r, p)
    nodes = [("g", g) for g in range(1, 28)] + [("e", bk, i) for bk in blks for i in (0, 1)]
    ends = {bk: block_ends(*bk, p, A, B) for bk in blks}
    val = lambda q: q[1] if q[0] == "g" else ends[q[1]][q[2]]
    idx = {q: i for i, q in enumerate(nodes)}
    D = len(nodes)  # dummy
    m = cp_model.CpModel()
    arcs, lit = [], {}

    def add(i, j):
        v = m.NewBoolVar(""); lit[(i, j)] = v; arcs.append((i, j, v))

    for q in nodes:
        for w in nodes:
            if q == w:
                continue
            same_block = q[0] == "e" and w[0] == "e" and q[1] == w[1]
            if same_block or odd_tri(val(q) + val(w)):
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
        return None, s.StatusName(st)
    succ = {i: j for (i, j, v) in arcs if s.Value(v)}
    order, cur = [], idx[("g", A)]
    while cur != D:
        order.append(nodes[cur]); cur = succ[cur]
    # compress to items: glue values, and blocks with orientation (False = first end first)
    items, k = [], 0
    while k < len(order):
        q = order[k]
        if q[0] == "g":
            items.append(("g", q[1])); k += 1
        else:
            items.append(("b", q[1], q[2] == 1)); k += 2
    return items, "OK"


if __name__ == "__main__":
    import sys, json, time
    A = 1; B = {0: int(sys.argv[1]), 1: int(sys.argv[2])}
    lo, hi = int(sys.argv[3]), int(sys.argv[4])
    res = {}
    t0 = time.time()
    for p in (0, 1):
        for r in range(lo, hi + 1):
            items, st = solve(r, p, A, B)
            res[f"{r},{p}"] = items
            if items is None:
                print("FAIL", r, p, st, flush=True)
    print("done", round(time.time() - t0, 1), "s; solved", sum(v is not None for v in res.values()), "of", len(res))
    json.dump({"A": A, "B": B, "layouts": res}, open(f"layouts_{B[0]}_{B[1]}_{lo}_{hi}.json", "w"))
    sys.exit(1 if any(v is None for v in res.values()) else 0)
