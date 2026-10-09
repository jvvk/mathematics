#!/usr/bin/env python3
"""Exact, independent checks for the order-three classification."""
from collections import Counter
from fractions import Fraction
from itertools import combinations, combinations_with_replacement, product
import json
import random


def game_wins(a, b, c):
    """Literal game: enumerate the enemy's singleton and pair choices."""
    return all(any(x + b[j] + z == 0 for j in pair for z in c)
               for x in a for pair in combinations(range(3), 2))


def gap_targets(p, q, c):
    c = sorted(set(c))
    assert c[0] == 0
    allowed = set()
    if len(c) == 1:
        return allowed
    r = c[1]
    if len(c) == 2:
        if r == p:
            allowed.add(p)
        if r == q or r == p + q:
            allowed.add(p + q)
        return allowed
    s = c[2] - r
    if p == r or p == r + s:
        allowed.add(p)
    if p == s:
        allowed.add(p + r)
    if q == r or q == r + s or p + q == r or p + q == r + s:
        allowed.add(p + q)
    if s == q or s == p + q:
        allowed.add(p + q + r)
    return allowed


def classified_wins(a, b, c):
    repeated = [x for x, count in Counter(b).items() if count >= 2]
    if repeated:
        return all(-x - repeated[0] in c for x in a)
    u, middle, top = sorted(b)
    v = min(c)
    allowed = gap_targets(middle - u, top - middle, [z - v for z in c])
    return all(-x - u - v in allowed for x in a)


def distinct_families(a, b, c):
    """Check membership in the five displayed families, without gap_targets."""
    u, v = min(b), min(c)
    aa = set(x + u + v for x in a)
    bb = tuple(sorted(x - u for x in b))
    cc = tuple(sorted(x - v for x in c))
    p, q = bb[1], bb[2] - bb[1]
    if cc == bb and aa == {-p, -p-q, -2*p-q}:
        return True
    h = bb[1]
    if bb == (0, h, 2*h):
        if cc == (0, h, 3*h) and aa == {-h, -2*h, -3*h}:
            return True
        if cc == (0, 2*h, 3*h) and aa == {-2*h, -3*h, -4*h}:
            return True
    if bb == (0, h, 3*h) and cc == (0, h, 2*h):
        return aa == {-h, -2*h, -3*h}
    h = bb[1] * Fraction(1, 2)
    if bb == (0, 2*h, 3*h) and cc == (0, h, 2*h):
        return aa == {-2*h, -3*h, -4*h}
    return False


def run():
    stats = Counter()
    rows = tuple(combinations_with_replacement(range(-3, 4), 3))
    for a, b, c in product(rows, repeat=3):
        actual = game_wins(a, b, c)
        predicted = classified_wins(a, b, c)
        assert actual == predicted, (a, b, c, actual, predicted)
        stats['integer_matrices'] += 1
        stats['integer_winning_matrices'] += actual
        if all(len(set(row)) == 3 for row in (a, b, c)):
            assert actual == distinct_families(a, b, c), (a, b, c)
            stats['distinct_integer_matrices'] += 1
            stats['distinct_integer_winning_matrices'] += actual

    gap_values = sorted(set(Fraction(n, d) for n in range(1, 9) for d in (1, 2, 3)))
    for p, q, r, s in product(gap_values, repeat=4):
        bb, cc = (0, p, p+q), (0, r, r+s)
        counts = Counter(x+y for x in bb for y in cc)
        actual = {x for x, n in counts.items() if n >= 2}
        assert actual == gap_targets(p, q, cc), (p, q, r, s)
        assert len(actual) <= 3, (p, q, r, s, actual)
        if len(actual) == 3:
            assert distinct_families(tuple(-x for x in actual), bb, cc)
            stats['three_target_gap_cases'] += 1
        stats['rational_gap_cases'] += 1

    rng = random.Random(453809)
    for _ in range(20000):
        a, b, c = tuple(tuple(Fraction(rng.randint(-8, 8), rng.randint(1, 5))
                             for _ in range(3)) for _ in range(3))
        assert game_wins(a, b, c) == classified_wins(a, b, c), (a, b, c)
        if all(len(set(row)) == 3 for row in (a, b, c)):
            assert game_wins(a, b, c) == distinct_families(a, b, c), (a, b, c)
        stats['random_rational_matrices'] += 1

    # Exercise all five families with nonintegral positive parameters and shifts.
    for p, q in product((Fraction(1, 3), Fraction(2, 5), Fraction(7, 2)), repeat=2):
        examples = [((-p, -p-q, -2*p-q), (0, p, p+q), (0, p, p+q))]
        h = p
        examples += [
            ((-h, -2*h, -3*h), (0, h, 2*h), (0, h, 3*h)),
            ((-2*h, -3*h, -4*h), (0, h, 2*h), (0, 2*h, 3*h)),
            ((-h, -2*h, -3*h), (0, h, 3*h), (0, h, 2*h)),
            ((-2*h, -3*h, -4*h), (0, 2*h, 3*h), (0, h, 2*h)),
        ]
        for a, b, c in examples:
            u, v = Fraction(5, 7), Fraction(-2, 3)
            shifted = (tuple(x-u-v for x in a), tuple(x+u for x in b),
                       tuple(x+v for x in c))
            assert game_wins(*shifted)
            assert classified_wins(*shifted)
            assert distinct_families(*shifted)
            stats['shifted_rational_family_examples'] += 1
    return dict(stats)


if __name__ == '__main__':
    result = {'passed': True, **run()}
    print(json.dumps(result, indent=2, sort_keys=True))
