"""Pairs of rooted binary trees on r leaves with MAST 2 (every triple resolved differently):
for each r, the minimum possible max(height X, height Y)."""
import itertools, sys

def trees(labels):
    """All rooted binary trees on a tuple of labels (nested tuples), each once."""
    if len(labels) == 1:
        yield labels[0]; return
    first, rest = labels[0], labels[1:]
    for k in range(0, len(rest)):
        for left_rest in itertools.combinations(rest, k):
            left = (first,) + left_rest
            right = tuple(x for x in rest if x not in left_rest)
            for L in trees(left):
                for R in trees(right):
                    yield (L, R)

def height(t):
    return 0 if not isinstance(t, tuple) else 1 + max(height(t[0]), height(t[1]))

def leaves(t):
    return [t] if not isinstance(t, tuple) else leaves(t[0]) + leaves(t[1])

def triples(t, r):
    """dict triple->index of the outgroup (the leaf separated from the cherry)."""
    out = {}
    def go(t):
        if not isinstance(t, tuple):
            return
        L, R = leaves(t[0]), leaves(t[1])
        for a, b in itertools.combinations(L, 2):
            for c in R: out[tuple(sorted((a, b, c)))] = c
        for a, b in itertools.combinations(R, 2):
            for c in L: out[tuple(sorted((a, b, c)))] = c
        go(t[0]); go(t[1])
    go(t)
    keys = list(itertools.combinations(range(r), 3))
    return tuple(out[k] for k in keys)

r_max = int(sys.argv[1])
for r in range(3, r_max + 1):
    ts = list(trees(tuple(range(r))))
    info = [(height(t), triples(t, r), t) for t in ts]
    best = None
    by_h = sorted(info, key=lambda x: x[0])
    for hx, tx, X in by_h:
        if best is not None and hx >= best[0]:
            break
        for hy, ty, Y in by_h:
            if max(hx, hy) >= (best[0] if best else 99):
                break
            if all(a != b for a, b in zip(tx, ty)):
                best = (max(hx, hy), X, Y)
                break
    print(r, len(ts), "min height of a MAST-2 pair:", best[0] if best else None, best[1:] if best else "")
    sys.stdout.flush()
