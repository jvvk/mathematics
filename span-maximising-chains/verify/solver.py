"""Globally solve a given instance using proved structural restrictions.

Lengths and angles must be strictly increasing and positive, with angle sum
strictly less than pi. Patterns use zero-based ranks and identify reversal pairs.
"""
from math import cos, sin, pi, isfinite


def patterns(n):
    if n < 1:
        raise ValueError('Need at least one segment.')
    if n == 1:
        yield (0,), ()
        return
    if n == 2:
        yield (0, 1), (0,)
        return
    for mask in range(1 << (n-3)):
        left = tuple(i for i in range(2, n-1) if mask >> (i-2) & 1)
        right = tuple(i for i in range(n-2, 1, -1) if not mask >> (i-2) & 1)
        p = (0,) + left + (n-1,) + right + (1,)
        for gap_mask in range(1 << (n-2)):
            left_gaps = tuple(i for i in range(n-2, 0, -1) if gap_mask >> (i-1) & 1)
            right_gaps = tuple(i for i in range(1, n-1) if not gap_mask >> (i-1) & 1)
            yield p, left_gaps + (0,) + right_gaps


def maximize(lengths, angles):
    """Return (distance, length-rank order, angle-rank order).

    Ordinary floating-point arithmetic is used; use certificate.py when exact
    certification for rational half-angle tangents is wanted.
    """
    n = len(lengths)
    if n < 1 or len(angles) != n-1:
        raise ValueError('Need n positive lengths and n-1 angles.')
    if any(not isfinite(x) or x <= 0 for x in (*lengths, *angles)):
        raise ValueError('All lengths and angles must be positive and finite.')
    if any(a >= b for a, b in zip(lengths, lengths[1:])) or any(a >= b for a, b in zip(angles, angles[1:])):
        raise ValueError('Lengths and angles must each be strictly increasing.')
    if sum(angles) >= pi:
        raise ValueError('The sum of angles must be strictly less than pi.')
    best = None
    for p, q in patterns(n):
        theta = 0.
        x, y = lengths[p[0]], 0.
        for i in range(1, n):
            theta += angles[q[i-1]]
            x += lengths[p[i]] * cos(theta)
            y += lengths[p[i]] * sin(theta)
        score = x*x + y*y
        if best is None or score > best[0]:
            best = score, p, q
    return best[0]**.5, best[1], best[2]


def conjectured_patterns(n):
    """Experimental recursive family, NOT a proved complete characterization.

    Its cardinality is 1,1,1,3,6,14,31,70,157,... for n=1,2,... .
    """
    if n <= 2:
        yield tuple(range(n)), tuple(range(n-1))
        return
    if n == 3:
        yield (0, 2, 1), (1, 0)
        return
    # Largest angle on the side of the smallest length. The first interior
    # length has rank k; strip one left endpoint and a right tail.
    for k in range(2, n):
        m = n-k+1
        for p, q in conjectured_patterns(m):
            pp = (0,) + tuple(i+k-1 for i in reversed(p)) + tuple(range(k-2, 0, -1))
            qq = (n-2,) + tuple(reversed(q)) + tuple(range(n-k, n-2))
            yield pp, qq
    # Largest angle on the side of the second smallest length.
    for p, q in conjectured_patterns(n-2):
        yield (0,) + tuple(i+2 for i in p) + (1,), (n-3,) + q + (n-2,)
