"""Independent recheck (written by Codex during the proof check; shares no code with ../*.py).
Enumerates every plane tree and every legal labelling for s <= 8 and checks the rows against the Omega formula;
checks integrality, positivity, symmetry, the Omega recurrence, Lemma 2 and Corollary 3 exactly for s <= 20."""
import sys as _sys
if not __debug__:
    _sys.exit("refusing to run under python -O: the checks are assertions")
from collections import Counter
from functools import lru_cache
from itertools import product
from fractions import Fraction as F
from math import comb, factorial

@lru_cache(None)
def forests(vertices):
    if vertices == 0:
        return ((),)
    return tuple((head,) + tail
                 for n in range(1, vertices + 1)
                 for head in shapes(n)
                 for tail in forests(vertices - n))

@lru_cache(None)
def shapes(vertices):
    return forests(vertices - 1)

@lru_cache(None)
def assignments(shape):
    if not shape:
        return ((2, 1),)
    out = []
    for children in product(*(assignments(c) for c in shape)):
        total = sum(lab for lab, nu in children)
        nu = sum(nu for lab, nu in children)
        out.extend((lab, nu + (lab == total + 2)) for lab in range(2, total + 3))
    return tuple(out)

def tree_row(edges):
    counts = Counter()
    for shape in shapes(edges + 1):
        for children in product(*(assignments(c) for c in shape)):
            counts[1 + sum(nu for lab, nu in children)] += 1
    assert set(counts) == set(range(2, edges + 2))
    return [counts[nu] for nu in range(2, edges + 2)]

def omega(k, m):
    ans = F(12**k, factorial(k + 1)*factorial(2*k + 1))
    for ell in range(1, k + 1):
        ans *= comb(m + 2*ell, 3)
    return ans

def numerator(k):
    degree = 3*k + 1
    return [sum((-1)**j*comb(degree, j)*omega(k, m-j)
                for j in range(min(m, degree)+1)) for m in range(degree+1)]

rows = {}
for s in range(1, 9):
    row = tree_row(s)
    rows[s] = row
    coeffs = numerator(s)
    assert coeffs == [0] + row + [0]*(2*s+1)
    print('explicit', s, 'shapes', len(shapes(s+1)), 'row', row, 'total', sum(row))

for s in range(1, 21):
    coeffs = numerator(s)
    assert all(c.denominator == 1 for c in coeffs)
    assert coeffs[0] == 0 and all(c == 0 for c in coeffs[s+1:])
    row = coeffs[1:s+1]
    assert all(c > 0 for c in row)
    assert row == row[::-1]
    assert row[0] == row[-1] == comb(2*s, s)//(s+1)
    assert sum(row) == F(2**s*factorial(3*s), factorial(s+1)*factorial(2*s+1))
    for m in range(101):
        assert (s+1)*(2*s)*(2*s+1)*omega(s,m) == 2*(m+2*s)*(m+2*s-1)*(m+2*s-2)*omega(s-1,m)
    # Independently form the two hypergeometric coefficients using rising products.
    def rising(a, r):
        ans = F(1)
        for j in range(r): ans *= a+j
        return ans
    for r in range(31):
        a = rising(s+F(1,2),r)*rising(s+1,r)*rising(s+F(3,2),r)/(rising(F(1,2),r)*rising(F(3,2),r)*factorial(r))
        b = rising(s+1,r)*rising(s+F(3,2),r)*rising(s+2,r)/(rising(F(3,2),r)*rising(2,r)*factorial(r))
        assert omega(s,2*r+1) == comb(2*s,s)//(s+1)*a
        assert omega(s,2*r+2) == 4**s*b
    # A401900: finite differences of Pi, compared to subset binomial counts.
    d = 3*s+1
    pi = [4**s*rising(F(r)+F(1,2),s)*rising(r+1,s)*rising(F(r)+F(3,2),s)/(factorial(s)*rising(F(3,2),s)*factorial(s+1)) for r in range(d+1)]
    dc = [sum((-1)**j*comb(d,j)*pi[k-j] for j in range(min(k,d)+1)) for k in range(d+1)]
    pairs = [sum(row[j]*comb(d,2*k-j) for j in range(s) if 0 <= 2*k-j <= d) for k in range(d+1)]
    assert dc == pairs
    if s <= 3: print('D', s, [int(c) for c in dc if c])
print('exact numerator degree, integrality, positivity, symmetry, extremes, totals: s=1..20 OK')
print('Omega recurrence: s=1..20, m=0..100 OK; Omega(0,0) =', omega(0,0))
print('hypergeometric identities: s=1..20, r=0..30 OK')
print('A401900 finite differences versus subset counts: n=1..20, k=0..3n+1 OK')
