"""Caterpillars as leaf orders: the 4 leaves at positions p1<p2<p3<p4 split p1p2|p3p4."""
from itertools import combinations


def cat_split(order: list[int], Q) -> frozenset:
    pos = {v: i for i, v in enumerate(order)}
    a, b, c, d = sorted(Q, key=pos.__getitem__)
    return frozenset([frozenset([a, b]), frozenset([c, d])])


def common(orders: list[list[int]]) -> list:
    X = sorted(orders[0])
    assert all(sorted(o) == X for o in orders)
    return [Q for Q in combinations(X, 4) if len({cat_split(o, Q) for o in orders}) == 1]


if __name__ == "__main__":
    sy = [[1, 2, 3, 4, 5, 6, 7, 8, 9], [1, 2, 7, 6, 5, 4, 3, 8, 9], [1, 8, 3, 6, 5, 4, 7, 2, 9]]
    print("Snir-Yuster k=3 example (first order read as 123456789): common quartets =", len(common(sy)))
