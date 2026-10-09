#!/usr/bin/env python3
"""Enumerate canonical maximal winning linear templates.

The general algorithm is finite at every n, but can grow very rapidly.
Order three has a faster equivalent enumeration of minimal zero patterns.
"""
from collections import Counter
from fractions import Fraction
from itertools import combinations, permutations, product
from pathlib import Path
import argparse
import json


def rref(rows, columns):
    a = [list(map(Fraction, row)) for row in rows]
    k = 0
    for j in range(columns):
        s = next((i for i in range(k, len(a)) if a[i][j]), None)
        if s is None:
            continue
        a[k], a[s] = a[s], a[k]
        pivot = a[k][j]
        a[k] = [x/pivot for x in a[k]]
        for i in range(len(a)):
            if i != k and a[i][j]:
                factor = a[i][j]
                a[i] = [x-factor*y for x, y in zip(a[i], a[k])]
        k += 1
        if k == len(a):
            break
    return tuple(tuple(row) for row in a[:k])


def edge_vectors(n):
    vectors = []
    for t in product(range(n), repeat=n):
        v = [0]*(n*n)
        for i, j in enumerate(t):
            v[n*i+j] = 1
        vectors.append(tuple(v))
    return tuple(vectors)


def contains(space, v):
    pivots = [next(j for j, x in enumerate(row) if x) for row in space]
    return all(v[j] == sum(v[p]*row[j] for p, row in zip(pivots, space))
               for j in range(len(v)))


def closure_mask(space, vectors):
    return sum(1 << k for k, v in enumerate(vectors) if contains(space, v))


def inclusion_minima(spaces, vectors):
    candidates = sorted((len(w), closure_mask(w, vectors), w) for w in set(spaces))
    kept = []
    for rank, mask, space in candidates:
        if not any(oldrank < rank and oldmask & mask == oldmask
                   for oldrank, oldmask, _ in kept):
            kept.append((rank, mask, space))
    return kept


def enumerate_general(n):
    vectors = edge_vectors(n)
    vector_by_tuple = dict(zip(product(range(n), repeat=n), vectors))
    spaces = {()}
    row_choices = [tuple(combinations(range(n), i+1)) for i in range(n)]
    for box in product(*row_choices):
        edges = [vector_by_tuple[t] for t in product(*box)]
        next_spaces = set()
        for space in spaces:
            if any(contains(space, v) for v in edges):
                next_spaces.add(space)
            else:
                next_spaces.update(rref(space+(v,), n*n) for v in edges)
        spaces = {space for _, _, space in inclusion_minima(next_spaces, vectors)}
    return inclusion_minima(spaces, vectors)


def enumerate_order_three():
    vectors = edge_vectors(3)
    menus = []
    # Each first-row position needs zero transversals at two different
    # second-row positions. Pick one third-row position for each.
    for a in range(3):
        menus.append([(vectors[9*a+3*b+c], vectors[9*a+3*d+e])
                      for b, d in combinations(range(3), 2)
                      for c, e in product(range(3), repeat=2)])
    spaces = {rref(tuple(v for pair in selected for v in pair), 9)
              for selected in product(*menus)}
    return inclusion_minima(spaces, vectors)


def records(n, components):
    return [{'dimension': n*n-rank, 'zero_pattern': mask,
             'equations': [[str(x) for x in row] for row in space]}
            for rank, mask, space in components]


def order_three_orbits(items):
    tuples = tuple(product(range(3), repeat=3))
    perms = tuple(permutations(range(3)))
    maps = [tuple(9*p[t[0]]+3*q[t[1]]+r[t[2]] for t in tuples)
            for p, q, r in product(perms, repeat=3)]
    orbits = {}
    for item in items:
        active = [i for i in range(27) if item['zero_pattern'] >> i & 1]
        key = min(sum(1 << mapping[i] for i in active) for mapping in maps)
        orbit = orbits.setdefault(key, {'dimension': item['dimension'],
                                       'count': 0, 'representative': item})
        orbit['count'] += 1
    return [orbits[key] for key in sorted(orbits)]


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('order', type=int)
    parser.add_argument('--general', action='store_true',
                        help='Use the slower box-by-box algorithm also at order three')
    args = parser.parse_args()
    if args.order < 1:
        parser.error('Order must be positive')
    n = args.order
    components = enumerate_order_three() if n == 3 and not args.general else enumerate_general(n)
    items = records(n, components)
    root = Path(__file__).resolve().parent
    (root/f'components-order-{n}.json').write_text(json.dumps(items, indent=2))
    result = {'order': n, 'maximal_components': len(items),
              'dimension_counts': dict(sorted(Counter(x['dimension'] for x in items).items()))}
    if n == 3:
        orbits = order_three_orbits(items)
        (root/'component-orbits-order-3.json').write_text(json.dumps(orbits, indent=2))
        result['row_permutation_orbits'] = len(orbits)
        result['orbit_dimension_counts'] = dict(sorted(Counter(x['dimension'] for x in orbits).items()))
    print(json.dumps(result, indent=2))
