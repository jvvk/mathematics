#!/usr/bin/env python3
"""Exact checks of the template enumeration and sharp-rank constructions."""
from collections import Counter
from fractions import Fraction
from itertools import combinations, combinations_with_replacement, product
from math import gcd, lcm
from pathlib import Path
import json

from templates import (contains, edge_vectors, enumerate_general,
                       enumerate_order_three, order_three_orbits, records, rref)
from verify_general import literal_game


def integer_equations(space):
    result = []
    for row in space:
        scale = lcm(*(x.denominator for x in row))
        integers = [int(x*scale) for x in row]
        divisor = gcd(*integers)
        result.append(tuple(x//divisor for x in integers))
    return tuple(result)


def template_membership(matrix, equations):
    flat = tuple(x for row in matrix for x in row)
    return any(all(sum(x*y for x, y in zip(flat, row)) == 0 for row in space)
               for space in equations)


def run():
    stats = {}
    for n, expected in ((1, 1), (2, 4)):
        result = enumerate_general(n)
        assert len(result) == expected
        assert all(n*n-len(w) <= n*(n+1)//2-1 for _, _, w in result)
        stats[f'order_{n}_components'] = len(result)

    fast = enumerate_order_three()
    general = enumerate_general(3)
    assert {(mask, w) for _, mask, w in fast} == {(mask, w) for _, mask, w in general}
    assert len(fast) == 1107
    counts = dict(Counter(9-rank for rank, _, _ in fast))
    assert counts == {5: 99, 4: 576, 3: 432}
    stats['order_3_components'] = len(fast)
    stats['order_3_dimension_counts'] = counts
    orbits = order_three_orbits(records(3, fast))
    assert len(orbits) == 12
    assert sum(orbit['count'] for orbit in orbits) == 1107
    stats['order_3_row_permutation_orbits'] = len(orbits)

    # Every listed component wins, using the original position boxes.
    vectors = edge_vectors(3)
    tuple_number = {t: i for i, t in enumerate(product(range(3), repeat=3))}
    boxes = [tuple(tuple_number[t] for t in product((a,), bpair, range(3)))
             for a in range(3) for bpair in combinations(range(3), 2)]
    for rank, mask, space in fast:
        assert rank == len(space)
        assert mask == sum(1 << i for i, v in enumerate(vectors) if contains(space, v))
        assert all(any(mask >> i & 1 for i in box) for box in boxes)
    # No component contains another: closure inclusion is span inclusion.
    for i, (_, mask, _) in enumerate(fast):
        assert not any(other & mask == other for j, (_, other, _) in enumerate(fast) if j != i)
    stats['irredundant_components_checked'] = len(fast)

    eqs = [integer_equations(space) for _, _, space in fast]
    rows = tuple(combinations_with_replacement((-1, 0, 1), 3))
    for matrix in product(rows, repeat=3):
        assert template_membership(matrix, eqs) == literal_game(matrix), matrix
    stats['literal_order_3_matrix_checks'] = len(rows)**3

    # A rank basis for the dominant-value construction at each order.
    for n in range(1, 11):
        base = tuple(1 if j % n == 0 else 0 for j in range(n*n))
        witnesses = [base]
        for i in range(n):
            for j in range(1, n-i):
                v = list(base)
                v[n*i] = 0
                v[n*i+j] = 1
                witnesses.append(tuple(v))
        rank = len(rref(witnesses, n*n))
        assert rank == n*(n-1)//2+1
        assert n*n-rank == n*(n+1)//2-1
    stats['sharp_dominant_constructions'] = 10

    # A rank basis for the paired construction, with all rows distinct.
    for n in (2, 4, 6, 8, 10):
        base = tuple(1 if j % n == 0 else 0 for j in range(n*n))
        witnesses = [base]
        for i in range(n//2):
            partner = n-1-i
            for j in range(1, n):
                v = list(base)
                v[n*i] = v[n*partner] = 0
                v[n*i+j] = v[n*partner+j] = 1
                witnesses.append(tuple(v))
        assert len(rref(witnesses, n*n)) == n*(n-1)//2+1
    stats['sharp_paired_constructions'] = 5

    examples = (
        [[0, 1], [-0, -1]],
        [[0, 1, 4, 9], [0, 2, 7, 11], [0, -2, -7, -11], [0, -1, -4, -9]],
        [[-6, -5, -4, -3], [0, 1, 2, 3], [0, 1, 2, 3], [0, 1, 2, 3]],
    )
    for matrix in examples:
        assert literal_game(matrix)
    stats['literal_structural_examples'] = len(examples)
    return stats


if __name__ == '__main__':
    print(json.dumps({'passed': True, **run()}, indent=2, sort_keys=True))
