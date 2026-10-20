"""h(4) >= 22: T, sT, s^2T, s^3T on 21 leaves share no quartet, s = (1 2 3 4)(5 6 7 8)(9 10 11 12)(13 14 15 16)
(17 18 19 20), 0 fixed. Found by cyclic1.py (SAT), 2026-10-16."""
import sys
sys.path.insert(0, __file__.rsplit("/", 1)[0])
from quartets import common_quartets, leaves

T = (0, (16, ((17, 10), (1, ((((((6, 14), 11), 5), ((3, 15), 8)), ((4, 13), (18, ((20, 7), 19)))), (9, (2, 12)))))))


def s(x: int) -> int:
    return x if x == 0 else 4 * ((x - 1) // 4) + (x % 4) + 1


def relabel(t, f):
    return f(t) if isinstance(t, int) else tuple(relabel(c, f) for c in t)


if __name__ == "__main__":
    assert [s(x) for x in range(21)] == [0, 2, 3, 4, 1, 6, 7, 8, 5, 10, 11, 12, 9, 14, 15, 16, 13, 18, 19, 20, 17]
    assert leaves(T) == frozenset(range(21))
    trees = [T]
    for _ in range(3):
        trees.append(relabel(trees[-1], s))
    assert relabel(trees[-1], s) == T
    c = common_quartets(trees)
    assert not c, c
    print("k=4 witness verified: 5985 quartets on 21 leaves, none common to all four trees, so h(4) >= 22")
