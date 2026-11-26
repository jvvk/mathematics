"""Target rows from A336110's Om formula: z B_k(z) = (1-z)^(3k+1) Sum_{m>=1} Om(k,m) z^m."""
import sys as _sys
if not __debug__:
    _sys.exit("refusing to run under python -O: the checks are assertions")
from fractions import Fraction
from math import comb, factorial
import sys
from brute import row

def Om(k, m):
    p = Fraction(12**k, factorial(k + 1) * factorial(2 * k + 1))
    for L in range(1, k + 1):
        p *= comb(m + 2 * L, 3)
    return p

def target(k):
    M = 3 * k + 3
    a = [Om(k, m) if m >= 1 else Fraction(0) for m in range(M + 1)]
    b = [sum((-1)**j * comb(3 * k + 1, j) * a[m - j] for j in range(0, min(m, 3 * k + 1) + 1)) for m in range(M + 1)]
    assert all(x == 0 for x in b[k + 1:]), b
    assert all(x.denominator == 1 for x in b[1:k + 1]), b
    return [int(x) for x in b[1:k + 1]]

N = int(sys.argv[1]) if len(sys.argv) > 1 else 10
for k in range(1, N + 1):
    t, r = target(k), row(k)
    print(k, t == r)
    assert t == r
print("rows agree for k <= %d" % N)
