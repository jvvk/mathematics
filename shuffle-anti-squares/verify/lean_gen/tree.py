"""Find a refutation tree for each cut position of V over the 'overlap -> equal' facts (Z3 for pruning).
Leaves are pure linear systems; the tree is later emitted as Lean by_cases + omega."""
import sys
import z3

RUNS = [(0, (1, 0, 0)), (1, (0, 0, 1)), (0, (0, 5, 0)), (1, (0, 0, 2)), (0, (1, 0, 0)),
        (1, (0, 0, 1)), (0, (0, 2, 0)), (1, (0, 0, 1)), (0, (0, 1, 0)), (1, (0, 0, 3))]  # (letter, coeffs of L,l,m)


def build(r: int):
    L, l, m, v, k = z3.Ints("L l m v k")
    base = [l >= 1, m == 2 * v + 1, 9 * l <= L, v >= 0, k >= 0]
    def ln(co):
        return co[0] * L + co[1] * l + co[2] * m
    c, co = RUNS[r]
    n_r = ln(co)
    base.append(k <= n_r)
    lin = [(c, n_r - k)] + [(cc, ln(cc2)) for cc, cc2 in RUNS[r + 1:] + RUNS[:r]] + [(c, k)]
    a = [z3.Int(f"a{i}") for i in range(len(lin))]
    for i, (_, n) in enumerate(lin):
        base += [a[i] >= 0, a[i] <= n]
    SA, SB, ZA, ZB, pa, pb = [], [], [], [], [], []
    sa = sb = za = zb = 0
    for i, (ci, n) in enumerate(lin):
        bi = n - a[i]
        if ci == 1:
            SA.append(sa); SB.append(sb); ZA.append(za); ZB.append(zb); pa.append(a[i]); pb.append(bi)
            sa = sa + a[i]; sb = sb + bi
        else:
            za = za + a[i]; zb = zb + bi
    base += [sa == sb, za == zb]
    facts = {}
    for i in range(len(SA)):
        for j in range(len(SB)):
            facts[(i, j)] = ([pa[i] > 0, pb[j] > 0, SA[i] < SB[j] + pb[j], SB[j] < SA[i] + pa[i]],
                             ZA[i] == ZB[j])
    return base, facts


def feasible(cons) -> bool:
    s = z3.Solver()
    s.add(cons)
    return s.check() == z3.sat


def branches(chosen, conds, E):
    out = []
    for t in range(len(conds)):
        out.append(chosen + conds[:t] + [z3.Not(conds[t])])
    out.append(chosen + conds + [E])
    return out


def search(base, facts, chosen, used, depth=0):
    """Return tree: ('leaf',) or (key, sub_0, ..., sub_4): branch t negates condition t, last adds E."""
    if not feasible(base + chosen):
        return ("leaf",)
    best, best_score = None, -1
    for key, (conds, E) in facts.items():
        if key in used:
            continue
        score = sum(not feasible(base + b) for b in branches(chosen, conds, E))
        if score > best_score:
            best, best_score = key, score
            if score == len(conds) + 1:
                break
    if best is None:
        raise RuntimeError("feasible with all facts: not a refutation")
    conds, E = facts[best]
    u = used | {best}
    return (best,) + tuple(search(base, facts, b, u, depth + 1) for b in branches(chosen, conds, E))


def size(t):
    return 1 if t[0] == "leaf" else sum(size(s) for s in t[1:])


if __name__ == "__main__":
    import pickle
    for r in map(int, sys.argv[1:]):
        base, facts = build(r)
        t = search(base, facts, [], frozenset())
        print(r, "leaves", size(t), flush=True)
        pickle.dump(t, open(f"tree_{r}.pkl", "wb"))
