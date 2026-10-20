"""Cyclic form of the h(3) >= 14 certificate: leaves Z_13, sigma(x) = 3x mod 13 (order 3).
The tree T below, with sigma(T) and sigma^2(T), shares no quartet split. Found by cyclic.py (SAT), 2026-10-16."""
import sys
sys.path.insert(0, __file__.rsplit("/", 1)[0])
from quartets import common_quartets, leaves, quartet_map

T = (0, (1, (((8, 11), ((5, (4, 6)), ((3, 9), (12, (7, 10))))), 2)))


def relabel(t, f):
    return f(t) if isinstance(t, int) else tuple(relabel(c, f) for c in t)


def sigma(x: int) -> int:
    return 3 * x % 13


if __name__ == "__main__":
    assert leaves(T) == frozenset(range(13))
    T2 = relabel(T, sigma)
    T3 = relabel(T2, sigma)
    assert relabel(T3, sigma) == T, "sigma has order 3 on T's labels"
    c = common_quartets([T, T2, T3])
    assert not c, c
    # the SAT run's second and third trees are sigma(T) and sigma^2(T) as quartet systems
    S2 = (0, ((((11, 7), ((2, (12, 5)), (((4, 8), 10), (1, 9)))), 6), 3))
    S3 = (0, ((((7, 8), ((6, (2, 10)), ((4, (11, 12)), (1, 3)))), 5), 9))
    assert quartet_map(S2) == quartet_map(T2) and quartet_map(S3) == quartet_map(T3)
    print("cyclic witness verified: T, 3T, 9T on Z_13 share no quartet, so h(3) >= 14")
