"""Rigorous version of certify.py: interval arithmetic throughout and exact rational (a, c).

Claim checked: min over the simplex {x1..x4 >= 0, sum = 1} of max(options) >= 1, where the options are
  4^c (x1^a + x4^a), 4^c (x2^a + x3^a), 2^c (x1+x2)^a, 2^c (x3+x4)^a, 2^c (x1+x3)^a, 2^c (x2+x4)^a.
Every option is nondecreasing in each of x1..x4, so on a box [l, u] of (x1, x2, x3) with
x4 = 1 - x1 - x2 - x3 each option is at least its value at (l1, l2, l3, max(0, 1 - u1 - u2 - u3)).
Box corners are exact dyadic rationals. Each option is evaluated as an mpmath interval, and a box is
accepted only when the LOWER endpoint of some option's interval is >= 1. No margins, no floats.

Usage: certify_iv.py a_num/a_den c_num/c_den      e.g.  certify_iv.py 2/5 33/400   (exponent a - 2c)
"""

from __future__ import annotations

import sys
from fractions import Fraction as F

from mpmath import iv

iv.dps = 40


def rat(s: str) -> F:
    return F(s)


A, C = rat(sys.argv[1]), rat(sys.argv[2])
a_iv = iv.mpf(A.numerator) / A.denominator
c_iv = iv.mpf(C.numerator) / C.denominator
W4 = iv.exp(c_iv * iv.log(4))
W2 = iv.exp(c_iv * iv.log(2))
_cache: dict[F, object] = {}


def pw(x: F):
    """Interval enclosing x^a for an exact rational x >= 0."""
    if x == 0:
        return iv.mpf(0)
    if x not in _cache:
        _cache[x] = iv.exp(a_iv * iv.log(iv.mpf(x.numerator) / x.denominator))
    return _cache[x]


def certified(l, u) -> bool:
    x1, x2, x3 = l
    x4 = max(F(0), 1 - sum(u))
    options = (
        W4 * (pw(x1) + pw(x4)),
        W4 * (pw(x2) + pw(x3)),
        W2 * pw(x1 + x2),
        W2 * pw(x3 + x4),
        W2 * pw(x1 + x3),
        W2 * pw(x2 + x4),
    )
    return any(o.a >= 1 for o in options)  # .a is the lower endpoint


def main() -> None:
    stack = [((F(0),) * 3, (F(1),) * 3)]
    boxes, finest = 0, F(1)
    while stack:
        l, u = stack.pop()
        if sum(l) > 1:
            continue  # box misses the simplex
        boxes += 1
        if certified(l, u):
            continue
        w = [u[i] - l[i] for i in range(3)]
        i = max(range(3), key=lambda k: w[k])
        if w[i] < F(1, 2**22):
            print("FAILED near", [float(x) for x in l])
            sys.exit(1)
        finest = min(finest, w[i])
        m = (l[i] + u[i]) / 2
        stack.append((l, u[:i] + (m,) + u[i + 1 :]))
        stack.append((l[:i] + (m,) + l[i + 1 :], u))
    print(
        f"CERTIFIED (interval arithmetic) a={A} c={C} exponent a-2c={A - 2 * C} = {float(A - 2 * C)}  "
        f"boxes={boxes} finest width={float(finest):.2e}"
    )


if __name__ == "__main__":
    main()
