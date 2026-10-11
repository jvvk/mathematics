#!/usr/bin/env python3
"""Exact-arithmetic checks for 'Four Acute Faces' (standard library only).

Usage: python3 check_identities.py [--samples 400] [--seed 19]
MUTANT=1 (environment) calls a signed sum short when its squared length is below 3/2 instead of 1;
MUTANT=2 uses 3/4 for the integral of sqrt(u) over [0,1]. Each must fail.
Boundary configurations are excluded as in the paper. The sign correspondence
and the corner shapes are checked exhaustively.
"""
import argparse
from collections import Counter
from fractions import Fraction as F
from itertools import combinations, product
import json
import os
import random

MUTANT = os.environ.get('MUTANT', '0')
THRESHOLD = F(3, 2) if MUTANT == '1' else F(1)

ZERO = (F(0),) * 3
FACES = tuple(combinations(range(4), 3))
CHOICES = tuple((1,) + s for s in product((1, -1), repeat=3))
ROWS = tuple(s for s in CHOICES if sum(x < 0 for x in s) % 2 == 0)
COLS = tuple(s for s in CHOICES if sum(x < 0 for x in s) % 2 == 1)


def dot(a, b):
    return sum(x * y for x, y in zip(a, b))


def add(*vectors):
    return tuple(sum(coords) for coords in zip(*vectors))


def scale(t, a):
    return tuple(t * x for x in a)


def norm2(a):
    return dot(a, a)


def label(face, signs):
    """Keep face/sign labels distinct; identify only overall sign reversal."""
    signs = tuple(signs)
    if signs[0] < 0:
        signs = tuple(-x for x in signs)
    return tuple(face), signs


ENTRIES = frozenset(label(f, s) for f in FACES
                    for s in product((1, -1), repeat=3))
VERTEX_LABELS = {s: frozenset(label(f, (s[i] for i in f)) for f in FACES)
                 for s in CHOICES}
CELLS = {}
for i, row in enumerate(ROWS):
    for j, col in enumerate(COLS):
        common = VERTEX_LABELS[row] & VERTEX_LABELS[col]
        assert len(common) == 1
        CELLS[i, j] = next(iter(common))
assert len(set(CELLS.values())) == len(ENTRIES) == 16


def check_signs():
    for s in CHOICES:
        angles = {label(f, (-s[i] if i == v else s[i] for i in f))
                  for f in FACES for v in f}
        assert len(VERTEX_LABELS[s]) == 4 and len(angles) == 12
        assert not (VERTEX_LABELS[s] & angles)
        assert VERTEX_LABELS[s] | angles == ENTRIES
    for e in ENTRIES:
        pair = [s for s in CHOICES if e in VERTEX_LABELS[s]]
        assert len(pair) == 2
        assert sum(a != b for a, b in zip(*pair)) in (1, 3)
        assert {sum(x < 0 for x in s) % 2 for s in pair} == {0, 1}
    # The criterion's count rule, for every subset of marked entries.
    entries = sorted(ENTRIES)
    cell_for = {e: cell for cell, e in CELLS.items()}
    for flags in product((False, True), repeat=16):
        marked = {e for e, flag in zip(entries, flags) if flag}
        eligible = sum(marked <= VERTEX_LABELS[s] for s in CHOICES)
        if not marked:
            assert eligible == 8
        elif len(marked) == 1:
            assert eligible == 2
        else:
            rows = {cell_for[e][0] for e in marked}
            cols = {cell_for[e][1] for e in marked}
            assert eligible == int(len(rows) == 1) + int(len(cols) == 1)


def corner_counts(marked):
    row_k = [sum(i == r for i, j in marked) for r in range(4)]
    col_k = [sum(j == c for i, j in marked) for c in range(4)]
    row_N = sum(all(i == r for i, j in marked) for r in range(4))
    col_N = sum(all(j == c for i, j in marked) for c in range(4))
    row_C = sum(k in (1, 2) for k in row_k)
    col_C = sum(k in (1, 2) for k in col_k)
    r = sum(k > 0 for k in row_k)
    c = sum(k > 0 for k in col_k)
    assert 1 <= r <= 3 and 1 <= c <= 3
    assert row_N + row_C == (r - 1) + int(c <= 2) + int(r == 1)
    assert col_N + col_C == (c - 1) + int(r <= 2) + int(c == 1)
    assert row_N + col_N + row_C + col_C == 4
    return row_N + col_N, row_C + col_C


def check_corners():
    count = 0
    for widths in product(range(4), repeat=4):
        if any(widths[i] < widths[i + 1] for i in range(3)):
            continue
        if not 1 <= sum(widths) <= 4 or sum(w > 0 for w in widths) > 3:
            continue
        marked = {(i, j) for i, w in enumerate(widths) for j in range(w)}
        corner_counts(marked)
        count += 1
    assert count == 9
    return count


def det3(vs):
    a, b, c = vs
    return (a[0] * (b[1] * c[2] - b[2] * c[1])
            - a[1] * (b[0] * c[2] - b[2] * c[0])
            + a[2] * (b[0] * c[1] - b[1] * c[0]))


def rational_unit(rng):
    """Inverse stereographic projection; samples are exact, not uniform."""
    p = F(rng.randint(-40, 40), rng.randint(1, 40))
    q = F(rng.randint(-40, 40), rng.randint(1, 40))
    d = 1 + p * p + q * q
    return 2 * p / d, 2 * q / d, (p * p + q * q - 1) / d


def check_configuration(A):
    assert len(A) == 4 and all(norm2(a) == 1 for a in A)
    lengths = {e: norm2(add(*(scale(t, A[i]) for i, t in zip(*e))))
               for e in ENTRIES}
    if any(length == 1 for length in lengths.values()):
        return None
    short = {e for e, length in lengths.items() if length < THRESHOLD}
    assert 1 <= len(short) <= 4
    assert all(sum(e[0] == f for e in short) <= 1 for f in FACES)
    totals = {s: add(*(scale(t, a) for t, a in zip(s, A))) for s in CHOICES}
    x = [norm2(totals[s]) for s in ROWS]
    y = [norm2(totals[s]) for s in COLS]
    marked = set()
    for cell, e in CELLS.items():
        i, j = cell
        assert x[i] + y[j] == 2 * lengths[e] + 2
        assert (lengths[e] < 1) == (x[i] + y[j] < 4)
        if lengths[e] < 1:
            marked.add(cell)
    ir = sorted(range(4), key=lambda i: x[i])
    jc = sorted(range(4), key=lambda j: y[j])
    sorted_marks = {(ir.index(i), jc.index(j)) for i, j in marked}
    for i, j in sorted_marks:
        assert all((a, b) in sorted_marks
                   for a in range(i + 1) for b in range(j + 1))
        assert i + j <= 2
    N = C = 0
    ks = []
    for s in CHOICES:
        B = [scale(t, a) for t, a in zip(s, A)]
        S = totals[s]
        face_squares = [norm2(add(S, scale(-1, b))) for b in B]
        assert sum(face_squares) / 4 == 1 + norm2(S) / 2
        k = sum(length < 1 for length in face_squares)
        assert k <= 3
        assert k == len(VERTEX_LABELS[s] & short)
        assert int(k in (1, 2)) == k - k * (k - 1) // 2
        acute = True
        for f in FACES:
            for v in f:
                i, j = [t for t in f if t != v]
                angle_dot = dot(add(B[i], scale(-1, B[v])),
                                add(B[j], scale(-1, B[v])))
                test = add(B[i], B[j], scale(-1, B[v]))
                assert 2 * angle_dot == norm2(test) - 1
                acute = acute and angle_dot > 0
        assert acute == (short <= VERTEX_LABELS[s])
        N += int(acute)
        C += int(k in (1, 2))
        ks.append(k)
    assert N + C == 4
    assert N == 4 + sum(k * (k - 3) // 2 for k in ks)
    assert corner_counts(sorted_marks) == (N, C)
    # Alternating minors give a linear relation among the four vectors.
    coeff = [(-1) ** i * det3([A[j] for j in range(4) if j != i])
             for i in range(4)]
    weighted = any(coeff)
    if weighted:
        assert add(*(scale(t, a) for t, a in zip(coeff, A))) == ZERO
        B = [scale(1 if t >= 0 else -1, a) for t, a in zip(coeff, A)]
        w = [abs(t) / sum(abs(u) for u in coeff) for t in coeff]
        beta = [F(1, 2) - t for t in w]
        S = add(*B)
        assert all(t >= 0 for t in beta) and sum(beta) == 1
        assert add(*(scale(t, b) for t, b in zip(w, B))) == ZERO
        assert add(*(scale(t, b) for t, b in zip(beta, B))) == scale(F(1, 2), S)
        assert sum(t * norm2(add(S, scale(-1, b))) for t, b in zip(beta, B)) == 1
    return N, weighted


def check_example():
    A = [tuple(F(t, 3) for t in a) for a in
         [(-2, -1, 2), (3, 0, 0), (-2, 1, 2), (-1, 2, 2)]]
    assert check_configuration(A)[0] == 1
    # Flipping c repairs the face acd.
    a, b, c, d = A
    assert norm2(add(a, d, scale(-1, c))) == F(5, 9)
    flipped_face = (a, scale(-1, c), d)
    expected = [F(17, 9), F(65, 9), F(21, 9)]
    for vertex, square in enumerate(expected):
        test = add(*(scale(-1 if i == vertex else 1, point)
                     for i, point in enumerate(flipped_face)))
        assert norm2(test) == square > 1
        other = [i for i in range(3) if i != vertex]
        angle_dot = dot(add(flipped_face[other[0]], scale(-1, flipped_face[vertex])),
                        add(flipped_face[other[1]], scale(-1, flipped_face[vertex])))
        assert angle_dot == (square - 1) / 2 > 0
    assert norm2(add(*flipped_face)) == F(5, 9)
    assert add(*(scale(t, a) for t, a in zip((3, -2, -9, 6), A))) == ZERO
    B = [scale(t, a) for t, a in zip((1, -1, -1, 1), A)]
    S = add(*B)
    assert S == (F(-4, 3), F(0), F(2, 3)) and norm2(S) == F(20, 9)
    lengths = [norm2(add(S, scale(-1, b))) for b in B]
    assert lengths == [F(5, 9), F(5, 9), F(53, 9), F(13, 9)]
    assert sum(lengths) / 4 == F(19, 9) == 1 + norm2(S) / 2
    w = [F(t, 20) for t in (3, 2, 9, 6)]
    beta = [F(1, 2) - t for t in w]
    assert beta == [F(t, 20) for t in (7, 8, 1, 4)]
    assert sum(t * length for t, length in zip(beta, lengths)) == 1


def check_probability_algebra():
    # Using integral_0^1 sqrt(u) du=2/3 and integral_0^1 u du=1/2.
    root = F(3, 4) if MUTANT == '2' else F(2, 3)
    alpha = (1 - root) / 2
    gamma = (1 - 2 * root + F(1, 2)) / 4
    assert alpha == F(1, 6) and gamma == F(1, 24)
    assert gamma == alpha - F(1, 8)
    p = F(1, 2) + 6 * gamma - 4 * alpha
    assert p == 2 * alpha - F(1, 4) == F(1, 12)
    assert 4 * alpha - 6 * gamma == F(5, 12)
    return alpha, gamma, p


def main():
    if not __debug__:
        raise RuntimeError('Run without -O: these checks require assertions.')
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--samples', type=int, default=400)
    parser.add_argument('--seed', type=int, default=19)
    args = parser.parse_args()
    if args.samples < 1:
        parser.error('--samples must be positive')
    check_signs()
    corners = check_corners()
    check_example()
    alpha, gamma, p = check_probability_algebra()
    rng = random.Random(args.seed)
    histogram = Counter()
    checked = skipped = weighted = 0
    for _ in range(args.samples):
        result = check_configuration([rational_unit(rng) for _ in range(4)])
        if result is None:
            skipped += 1
        else:
            checked += 1
            histogram[result[0]] += 1
            weighted += int(result[1])
    if checked == 0:
        raise RuntimeError('No nonboundary configuration was tested.')
    print(json.dumps({'status': 'passed', 'seed': args.seed,
                      'exact_configurations': checked,
                      'boundary_configurations_skipped': skipped,
                      'cofactor_weight_checks': weighted,
                      'rank_deficient_cofactor_checks_skipped': checked - weighted,
                      'counts_by_N': dict(sorted(histogram.items())),
                      'all_corner_shapes': corners, 'all_sign_subsets': 2 ** 16,
                      'angle_first_example': 'passed (5/9 short face sum; 17/9,65/9,21/9 acute angle tests)',
                      'alpha': str(alpha), 'gamma': str(gamma), 'p': str(p)}, indent=2))


if __name__ == '__main__':
    main()
