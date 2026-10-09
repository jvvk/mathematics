#!/usr/bin/env python3
"""Exact finite solver for MO 453809 at arbitrary order.

Input: a JSON square matrix, with integer or rational-string entries.
Example: python3 general_solver.py example.json
Returns an exact decision and a legal adversary counterexample when losing.
No polynomial-time guarantee: the decision problem is Pi_2^P-complete.
"""
from collections import Counter
from fractions import Fraction
from itertools import combinations
import json
import sys


def exact_matrix(matrix):
    n = len(matrix)
    if n < 1 or any(len(row) != n for row in matrix):
        raise ValueError('Expected a nonempty square matrix')
    if any(not isinstance(x, (int, str, Fraction)) or isinstance(x, bool)
           for row in matrix for x in row):
        raise ValueError('Entries must be integers or exact rational strings')
    return tuple(tuple(Fraction(x) for x in row) for row in matrix)


def minimal_supports(row, count):
    """Minimal sets of values in which count positions can be selected."""
    multiplicities = Counter(row)
    values = sorted(multiplicities)
    menus = []
    for size in range(1, min(count, len(values)) + 1):
        for support in combinations(values, size):
            capacity = sum(multiplicities[x] for x in support)
            if capacity >= count and all(capacity-multiplicities[x] < count
                                         for x in support):
                menus.append(frozenset(support))
    return tuple(menus)


def positions_for_support(row, count, support):
    """Realize a minimal support by a legal selection of positions."""
    indices = [next(j for j, x in enumerate(row) if x == value)
               for value in sorted(support)]
    indices += [j for j, x in enumerate(row)
                if x in support and j not in indices][:count-len(indices)]
    assert len(indices) == count
    assert {row[j] for j in indices} == set(support)
    return tuple(sorted(indices))


def solve(matrix):
    matrix = exact_matrix(matrix)
    n = len(matrix)
    # Map each possible sumset to one adversary selection realizing it.
    frontier = {frozenset({Fraction(0)}): ()}
    widths = []
    for row_index in range(n-1, 0, -1):
        count = row_index + 1
        menus = minimal_supports(matrix[row_index], count)
        candidates = {}
        for support in menus:
            selected = positions_for_support(matrix[row_index], count, support)
            for suffix, witness in frontier.items():
                sums = frozenset(x+y for x in support for y in suffix)
                candidates.setdefault(sums, (selected,) + witness)
        # Supersets impose weaker membership requirements and remain weaker
        # under all earlier Minkowski additions. Keep the inclusion minima.
        frontier = {}
        for sums in sorted(candidates, key=lambda x: (len(x), tuple(sorted(x)))):
            if not any(smaller <= sums for smaller in frontier):
                frontier[sums] = candidates[sums]
        widths.append({'row': count, 'minimal_menus': len(menus),
                       'candidate_sumsets': len(candidates),
                       'minimal_sumsets': len(frontier)})

    allowed = set.intersection(*(set(x) for x in frontier))
    losing_selection = None
    for j, a in enumerate(matrix[0]):
        if -a not in allowed:
            bad_sums = next(x for x in frontier if -a not in x)
            losing_selection = ((j,),) + frontier[bad_sums]
            assert find_reply(matrix, losing_selection) is None
            break
    return {
        'winning': losing_selection is None,
        'allowed_first_row_values': sorted(-x for x in allowed),
        'losing_selection': losing_selection,
        'frontier_widths': widths,
    }


def find_reply(matrix, selection):
    """Return a zero-sum response to one legal selection, or None."""
    matrix = exact_matrix(matrix)
    if len(selection) != len(matrix):
        raise ValueError('One enemy selection is required for every row')
    sums = {Fraction(0): ()}
    for i, (row, selected) in enumerate(zip(matrix, selection)):
        if len(selected) != i+1 or len(set(selected)) != i+1:
            raise ValueError('Wrong number of selected positions')
        if any(j < 0 or j >= len(matrix) for j in selected):
            raise ValueError('Selected position out of range')
        next_sums = {}
        for total, reply in sums.items():
            for j in selected:
                next_sums.setdefault(total+row[j], reply+(j,))
        sums = next_sums
    return sums.get(Fraction(0))


def binary_normal_form(matrix):
    """Return fixed, universal, and existential choices for binary-valued rows."""
    matrix = exact_matrix(matrix)
    fixed, universal, existential = [], [], []
    for i, row in enumerate(matrix, start=1):
        multiplicities = Counter(row)
        values = tuple(sorted(multiplicities))
        if len(values) > 2:
            raise ValueError('A row has more than two distinct values')
        if len(values) == 1:
            fixed.append(values[0])
            continue
        forceable = tuple(x for x in values if multiplicities[x] >= i)
        if len(forceable) == 2:
            universal.append(values)
        elif len(forceable) == 1:
            fixed.append(forceable[0])
        else:
            existential.append(values)
    return tuple(fixed), tuple(universal), tuple(existential)


def embed_quantified_sum(universal, existential, target):
    """Embed forall-u exists-e [sum choices == target] in a square matrix."""
    m = max(len(universal)+1, len(existential), 1)
    n = 2*m
    rows = [[-target]*n]
    rows += [[x]*m + [y]*m for x, y in universal]
    rows += [[0]*n for _ in range(m-len(rows))]
    rows += [[x]*m + [y]*m for x, y in existential]
    rows += [[0]*n for _ in range(n-len(rows))]
    return rows


if __name__ == '__main__':
    if len(sys.argv) != 2:
        raise SystemExit('Usage: python3 general_solver.py matrix.json')
    with open(sys.argv[1]) as source:
        result = solve(json.load(source))
    result['allowed_first_row_values'] = [str(x) for x in result['allowed_first_row_values']]
    result['selection_indices_are_zero_based'] = True
    print(json.dumps(result, indent=2))
