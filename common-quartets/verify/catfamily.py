"""Explicit caterpillar family on 2^k+1 leaves with no common quartet (so h*(k) >= 2^k+2, hence h(k) >= 2^k+2).
Leaves -h..h, h = 2^(k-1). pi_1 = identity order. For b = 0..k-2, pi_(b+2) swaps labels -d and d (d = 1..h)
exactly when bit b of d-1 is 0."""
import sys
from itertools import combinations

sys.path.insert(0, __file__.rsplit("/", 1)[0])


def family(k: int) -> list[list[int]]:
    h = 2 ** (k - 1)
    orders = [list(range(-h, h + 1))]
    for b in range(k - 1):
        D = {d for d in range(1, h + 1) if not (d - 1) >> b & 1}
        orders.append([(-p if abs(p) in D else p) for p in range(-h, h + 1)])
    return orders


def count_common(orders: list[list[int]]) -> int:
    # fast: positions arrays; quartet common iff the pairing by position is identical in all orders
    n = len(orders[0])
    pos = [{v: i for i, v in enumerate(o)} for o in orders]
    X = orders[0]
    c = 0
    for Q in combinations(X, 4):
        key = None
        ok = True
        for p in pos:
            s = sorted(Q, key=p.__getitem__)
            pr = frozenset([frozenset(s[:2]), frozenset(s[2:])])
            if key is None:
                key = pr
            elif pr != key:
                ok = False
                break
        c += ok
    return c


if __name__ == "__main__":
    for k in range(2, int(sys.argv[1]) + 1 if len(sys.argv) > 1 else 6):
        F = family(k)
        c = count_common(F)
        print(f"k={k}: {len(F)} caterpillars on {2**k+1} leaves, common quartets = {c}", flush=True)
        assert c == 0
        if k <= 5:  # every order is needed: dropping any one leaves a common quartet
            for j in range(k):
                assert count_common(F[:j] + F[j + 1:]) > 0 if k > 1 else True
