"""Exact, standard-library-only verification of the 12-fold Spectre cover.

Run: python3 mo-516016/verify.py
The certificate is read next to this script. No optimizer is used.
"""
import json
from collections import Counter
from pathlib import Path

HERE = Path(__file__).resolve().parent
data = json.loads((HERE / 'certificate.json').read_text())
K = data['K']
placements = data['placements']

def add(a, b):
    return tuple(x + y for x, y in zip(a, b))

def rotate(a):
    # Multiplication by zeta, using zeta^4 = zeta^2 - 1.
    a0, a1, a2, a3 = a
    return (-a3, a0, a1 + a3, a2)

def rot(a, r):
    for _ in range(r % 12):
        a = rotate(a)
    return a

def quotient(a):
    return tuple(sum(x*y for x, y in zip(row, a)) for row in K)

zero = (0, 0, 0, 0)
one = (1, 0, 0, 0)
directions = (0, 10, 1, 3, 0, 2, 5, 7, 4, 6, 6, 8, 11, 9)
vertices = [zero]
for d in directions:
    vertices.append(add(vertices[-1], rot(one, d)))
assert vertices[-1] == zero

# These are an integer right inverse of K and an integer basis of ker K.
a = (0, 0, 1, 1)
b = (-2, -1, 0, -1)
v = (3, 1, 2, 3)
w = (-4, -3, 3, 1)
assert quotient(a) == (1, 0) and quotient(b) == (0, 1)
assert quotient(v) == (0, 0) and quotient(w) == (0, 0)

# |det[a b v w]| = 1 proves that v,w generate the entire integer kernel.
from itertools import permutations
def det4(columns):
    total = 0
    for p in permutations(range(4)):
        inversions = sum(p[i] > p[j] for i in range(4) for j in range(i+1, 4))
        term = (-1)**inversions
        for i in range(4):
            term *= columns[p[i]][i]
        total += term
    return total
assert abs(det4((a, b, v, w))) == 1

balance = Counter()
forward = Counter()
backward = Counter()
seen = set()
for r, x, y, weight in placements:
    assert 0 <= r < 12 and weight == 1
    assert (r, x, y) not in seen
    seen.add((r, x, y))
    for i, d in enumerate(directions):
        # The same arbitrary curve gamma is traversed from its distinguished
        # start on even edges and from its distinguished end on odd edges.
        start = vertices[i + (i % 2)]
        qx, qy = quotient(rot(start, r))
        label = (r + d + 6*(i % 2)) % 12
        key = (label, x + qx, y + qy)
        sign = (-1)**i
        balance[key] += weight*sign
        (forward if sign == 1 else backward)[key] += weight

assert len(placements) == 54
assert forward == backward
assert all(value == 0 for value in balance.values())
assert sum(forward.values()) == sum(backward.values()) == 378

# Independent exact area calculation in Q(sqrt(3)). Represent p+q sqrt(3)
# by (p,q), with Fraction coefficients.
from fractions import Fraction as F
def scalar_mul(a, b):
    p,q = a; r,t = b
    return (p*r + 3*q*t, p*t + q*r)
def scalar_sub(a,b):
    return (a[0]-b[0],a[1]-b[1])
def physical(a):
    a0,a1,a2,a3 = map(F,a)
    return ((a0+a2/2,a1/2),(a3+a1/2,a2/2))
def cross(a,b):
    return scalar_sub(scalar_mul(a[0],b[1]),scalar_mul(a[1],b[0]))
area2=(F(0),F(0))
for p,q in zip(vertices,vertices[1:]):
    term=cross(physical(p),physical(q))
    area2=tuple(x+y for x,y in zip(area2,term))
assert area2 == (F(6), F(6))
cell_area=cross(physical(v),physical(w))
assert cell_area == (F(27,2),F(27,2))
assert tuple(54*x/2 for x in area2) == tuple(12*x for x in cell_area)

print('PASS: 54 distinct tile orbits; all 378 pairs of whole curved edges cancel.')
print('PASS: tile area = 3 + 3 sqrt(3); cell area = (27/2)(1 + sqrt(3)).')
print('PASS: constant covering multiplicity = 12.')
