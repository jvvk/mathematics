#!/usr/bin/env python3
"""Independent finite checks of the recursion and the two reductions."""
from collections import Counter
from fractions import Fraction
from itertools import combinations, combinations_with_replacement, product
import json
import random

from general_solver import (binary_normal_form, embed_quantified_sum,
                            find_reply, minimal_supports, solve)


def literal_game(matrix):
    """Direct positional enumeration of both players, without the solver."""
    n = len(matrix)
    enemy_rows = [tuple(combinations(range(n), i+1)) for i in range(n)]
    for selection in product(*enemy_rows):
        if not any(sum(matrix[i][j] for i, j in enumerate(reply)) == 0
                   for reply in product(*selection)):
            return False
    return True


def quantified_sum(universal, existential, target):
    """Direct enumeration of the quantified equation, without row menus."""
    return all(any(sum(us)+sum(es) == target for es in product(*existential))
               for us in product(*universal))


def binary_value(matrix):
    fixed, universal, existential = binary_normal_form(matrix)
    return quantified_sum(universal, existential, -sum(fixed))


def qbf_truth(p, r, clauses):
    def sat(assignment):
        return all(any(assignment[abs(lit)-1] == (lit > 0) for lit in clause)
                   for clause in clauses)
    return all(any(sat(u+e) for e in product((False, True), repeat=r))
               for u in product((False, True), repeat=p))


def qbf_to_sum(p, r, clauses):
    """Implementation of the decimal reduction in GENERAL.md."""
    k = len(clauses)
    weights = []
    for j in range(1, p+r+1):
        pair = []
        for b in (False, True):
            value = 10**(k+j-1)
            for ell, clause in enumerate(clauses):
                count = sum(abs(lit) == j and ((lit > 0) == b) for lit in clause)
                value += count * 10**ell
            pair.append(value)
        weights.append(tuple(pair))
    universal = weights[:p]
    existential = [(0, w) for pair in weights[p:] for w in pair]
    existential += [(0, c*10**ell) for ell in range(k) for c in (1, 2)]
    target = sum(10**(k+j) for j in range(p+r)) + sum(4*10**ell for ell in range(k))
    return universal, existential, target


def check_witness(matrix, result):
    selection = result['losing_selection']
    if result['winning']:
        assert selection is None
    else:
        assert tuple(map(len, selection)) == tuple(range(1, len(matrix)+1))
        assert all(len(set(row)) == len(row) for row in selection)
        assert not any(sum(matrix[i][j] for i, j in enumerate(reply)) == 0
                       for reply in product(*selection))
        assert find_reply(matrix, selection) is None


def run():
    stats = Counter()
    for n in (1, 2, 3):
        rows = tuple(combinations_with_replacement((-1, 0, 1), n))
        for matrix in product(rows, repeat=n):
            actual = literal_game(matrix)
            result = solve(matrix)
            assert result['winning'] == actual, matrix
            check_witness(matrix, result)
            stats['exhaustive_small_matrices'] += 1

    # Check the multiplicity/menu lemma against all actual position selections.
    for n in range(1, 8):
        for row in combinations_with_replacement((-1, 0, 1), n):
            for i in range(1, n+1):
                actual = {frozenset(row[j] for j in selected)
                          for selected in combinations(range(n), i)}
                minima = {s for s in actual if not any(t < s for t in actual)}
                assert set(minimal_supports(row, i)) == minima
                stats['row_menu_cases'] += 1

    rng = random.Random(453809)
    for n, count in ((4, 160), (5, 40)):
        for _ in range(count):
            matrix = [[Fraction(rng.randrange(-3, 4), rng.randrange(1, 4))
                       for _ in range(n)] for _ in range(n)]
            result = solve(matrix)
            assert result['winning'] == literal_game(matrix), matrix
            check_witness(matrix, result)
            stats['random_rational_matrices_orders_4_5'] += 1

    # The premature-intersection counterexample, and an order-five analogue.
    counterexample = [[0]*4, [0, -1, -2, -3], [0, 1, 2, 3], [0, 10, 20, 30]]
    analogue = [[0]*5, [0, -1, -2, -3, -4], [0]*5, [0, 1, 2, 3, 4], [0]*5]
    for matrix in (counterexample, analogue):
        assert solve(matrix)['winning'] and literal_game(matrix)
        stats['targeted_winning_matrices'] += 1
    suffixes = [set(c+d for c in selected for d in counterexample[3])
                for selected in combinations(counterexample[2], 3)]
    assert not set.intersection(*suffixes)

    binary_rows = tuple(row for row in combinations_with_replacement(range(-2, 3), 3)
                        if len(set(row)) <= 2)
    for matrix in product(binary_rows, repeat=3):
        assert binary_value(matrix) == literal_game(matrix), matrix
        stats['exhaustive_binary_order_3'] += 1
    for n in range(1, 8):
        for _ in range(100):
            matrix = []
            for i in range(n):
                u, v = rng.randrange(-3, 4), rng.randrange(-3, 4)
                copies = rng.randrange(n+1)
                matrix.append([u]*copies + [v]*(n-copies))
            assert binary_value(matrix) == solve(matrix)['winning'], matrix
            stats['random_binary_matrices_orders_1_to_7'] += 1

    # Direct positional testing of the copy embedding for small instances.
    for _ in range(180):
        p, q = rng.randrange(2), rng.randrange(3)
        universal = [tuple(rng.randrange(-3, 4) for _ in range(2)) for _ in range(p)]
        existential = [tuple(rng.randrange(-3, 4) for _ in range(2)) for _ in range(q)]
        target = rng.randrange(-5, 6)
        matrix = embed_quantified_sum(universal, existential, target)
        assert len(matrix) <= 4
        expected = quantified_sum(universal, existential, target)
        assert expected == literal_game(matrix) == solve(matrix)['winning']
        stats['embedding_positional_checks'] += 1

    # Exhaust all formulas of up to four clauses on one universal and two
    # existential variables, with three distinct variables per clause.
    all_clauses = [tuple(sign*j for sign, j in zip(signs, (1, 2, 3)))
                   for signs in product((-1, 1), repeat=3)]
    formulas = [(1, 2, clauses) for k in range(5)
                for clauses in combinations(all_clauses, k)]
    # Include short, repeated-literal, empty, and tautological clauses.
    formulas += [(1, 1, clauses) for clauses in (
        ((1, 2), (-1, -2)), ((1,), (2,)), ((1, 2), (1, -2)),
        ((1, 1, 1),), ((1, -1, 2),), ((),), ())]
    for p, r, clauses in formulas:
        expected = qbf_truth(p, r, clauses)
        universal, existential, target = qbf_to_sum(p, r, clauses)
        assert expected == quantified_sum(universal, existential, target)
        matrix = embed_quantified_sum(universal, existential, target)
        assert expected == solve(matrix)['winning']
        assert all(x >= 0 for row in matrix[1:] for x in row)
        assert all(len(set(row)) <= 2 for row in matrix)
        for row in matrix:
            counts = Counter(row)
            if len(counts) == 2:
                assert set(counts.values()) == {len(matrix)//2}
        stats['qbf_full_reduction_checks'] += 1
        stats['qbf_true_cases'] += expected
        stats['qbf_false_cases'] += not expected
        stats['maximum_reduced_matrix_order'] = max(stats['maximum_reduced_matrix_order'], len(matrix))
    return dict(stats)


if __name__ == '__main__':
    print(json.dumps({'passed': True, **run()}, indent=2, sort_keys=True))
