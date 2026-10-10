"""Exact checks for "Capped dice" (MSE 5149864). Every claim has a mutant that must fail.

    timeout 600 nice -n 15 ~/.venvs/main/bin/python check.py

Notation: k faces, cap r (k r >= 1), m = floor(1/r), staircase p* = (r,..,r, 1-mr, 0,..), q* = reversal of p*.
g_{p,q}(u, v) = sum_i (u p_i - v q_i)^+;  overlap = sum over words of min(P(w), Q(w)).

C1  one roll: g_{p,q}(1, t) <= g*(1, t) for every admissible pair, every t >= 0, k = 2..7. Both sides are piecewise
    linear and convex in t, g_{p,q} is convex in (p, q), so it suffices to test vertex pairs at every breakpoint and
    beyond the last one (exact).
C2  n rolls, dice mixed freely: overlap(star^n) <= overlap(D) for random admissible sequences D (exact), k = 3..5.
C3  k = 4, 1/3 < r < 1/2: overlap(star^n) equals the asker's closed form; n = 2, r = 2/5 gives 6/25.
C4  equality, k = 4: relabellings attain (n <= 4); n = 1 iff max(p_i, q_i) = r; the n = 2 family attains;
    random admissible pairs that are not relabellings lose strictly for n = 3, 4.
"""

from __future__ import annotations

import itertools
import random
import sys
from fractions import Fraction as Fr
from math import comb

random.seed(20261010)
results: list[bool] = []


def report(name: str, good: bool, caught: bool) -> None:
    results.append(good and caught)
    print(f"{'PASS' if good else 'FAIL'} {name}   (mutant {'caught' if caught else 'MISSED'})", flush=True)


def stair(k: int, r: Fr) -> tuple[tuple[Fr, ...], tuple[Fr, ...]]:
    p = tuple(max(Fr(0), min(r, 1 - i * r)) for i in range(k))
    return p, tuple(reversed(p))


def vertices(k: int, r: Fr) -> list[tuple[Fr, ...]]:
    m = int(1 / r)
    rem = 1 - m * r
    base = [r] * m + ([rem] if rem > 0 else [])
    base += [Fr(0)] * (k - len(base))
    return sorted(set(itertools.permutations(base)))


def g(p, q, t: Fr) -> Fr:
    return sum((max(Fr(0), a - t * b) for a, b in zip(p, q)), Fr(0))


def tail(p, q) -> Fr:  # slope-free limit t -> infinity: mass of p where q = 0
    return sum((a for a, b in zip(p, q) if b == 0), Fr(0))


def dominates(ref, k: int, r: Fr) -> bool:
    V = vertices(k, r)
    pairs = [(p, q) for p in V for q in V]
    ts = {Fr(0)} | {a / b for p, q in pairs for a, b in zip(p, q) if a > 0 and b > 0}
    ts |= {a / b for a, b in zip(*ref) if a > 0 and b > 0}
    return all(g(p, q, t) <= g(*ref, t) for p, q in pairs for t in ts) and all(
        tail(p, q) <= tail(*ref) for p, q in pairs)


def caps(k: int) -> list[Fr]:
    out = {Fr(1, j) + Fr(i, 97) for j in range(1, k + 1) for i in (0, 1, 5)}
    out |= {Fr(random.randint(1, 999), 1000) for _ in range(5)}
    return sorted(r for r in out if Fr(1, k) <= r <= 1)


# C1
good, caught = True, False
for k in range(2, 8):
    for r in caps(k):
        good &= dominates(stair(k, r), k, r)
        p, _ = stair(k, r)
        if 1 - r * (k - 1) < r and not dominates((p, p), k, r):  # mutant: q* not reversed
            caught = True
report("C1 staircase dominates every capped pair at every rate, k = 2..7", good, caught)


def random_adm(k: int, r: Fr) -> tuple[Fr, ...]:
    V = vertices(k, r)
    w = [Fr(random.randint(0, 6)) for _ in V]
    if sum(w) == 0:
        w[0] = Fr(1)
    return tuple(sum((wi * v[i] for wi, v in zip(w, V)), Fr(0)) / sum(w) for i in range(k))


def overlap(D) -> Fr:
    k = len(D[0][0])
    tot = Fr(0)
    for w in itertools.product(range(k), repeat=len(D)):
        P = Q = Fr(1)
        for (p, q), i in zip(D, w):
            P *= p[i]
            Q *= q[i]
        tot += min(P, Q)
    return tot


# C2
good, caught = True, False
for k in (3, 4, 5):
    for r in caps(k)[:4]:
        star = stair(k, r)
        shifted = (star[0], star[1][1:] + star[1][:1])  # mutant reference: q* rotated by one face
        for n in (1, 2, 3):
            base = overlap([star] * n)
            mut = overlap([shifted] * n)
            for _ in range(12 if k < 5 else 4):
                D = [(random_adm(k, r), random_adm(k, r)) for _ in range(n)]
                o = overlap(D)
                good &= base <= o
                caught |= mut > o or mut > base
report("C2 n rolls: the staircase has the least overlap among mixed dice, k = 3..5, n <= 3", good, caught)


def asker(n: int, r: Fr, middle: bool = True) -> Fr:
    s = 1 - 2 * r
    val = 2 * sum(comb(n, j) * s**j * r ** (n - j) for j in range(n // 2 + 1, n + 1))
    if middle and n % 2 == 0:
        val += comb(n, n // 2) * (r * s) ** (n // 2)
    return val


# C3
good, caught = True, False
for r in (Fr(34, 100), Fr(7, 20), Fr(2, 5), Fr(9, 20), Fr(49, 100)):
    pa, qa = (r, 1 - 2 * r, r, Fr(0)), (Fr(0), r, 1 - 2 * r, r)
    for n in range(1, 7):
        o = overlap([(pa, qa)] * n)
        good &= o == asker(n, r) == overlap([stair(4, r)] * n)
        caught |= n % 2 == 0 and o != asker(n, r, middle=False)
good &= overlap([stair(4, Fr(2, 5))] * 2) == Fr(6, 25)
report("C3 k = 4: staircase overlap = the asker's closed form; C_2(2/5) = 6/25", good, caught)


def is_relabel(p, q, r: Fr) -> bool:
    s = 1 - 2 * r
    return sorted(zip(p, q)) == sorted([(r, Fr(0)), (r, s), (s, r), (Fr(0), r)])


# C4
good, caught = True, False
for r in (Fr(7, 20), Fr(2, 5), Fr(9, 20)):
    s = 1 - 2 * r
    star = stair(4, r)
    for perm in itertools.permutations(range(4)):
        pr = tuple(star[0][i] for i in perm), tuple(star[1][i] for i in perm)
        for n in (1, 2, 3, 4):
            good &= overlap([pr] * n) == overlap([star] * n)
    for x in (Fr(0), s / 3, s / 2, s):
        fam = ((r, r, x, s - x), (Fr(0), s, r, r))
        good &= overlap([fam] * 2) == overlap([star] * 2)
        if 0 < x < s and overlap([fam] * 3) == overlap([star] * 3):  # mutant: family attains at n = 3
            caught = True
    for _ in range(40):
        p, q = random_adm(4, r), random_adm(4, r)
        good &= (overlap([(p, q)]) == overlap([star])) == all(max(a, b) == r for a, b in zip(p, q))
        if not is_relabel(p, q, r):
            good &= overlap([(p, q)] * 3) > overlap([star] * 3)
            good &= overlap([(p, q)] * 4) > overlap([star] * 4)
    fam = ((r, r, s / 2, s / 2), (Fr(0), s, r, r))
    caught |= overlap([fam] * 3) > overlap([star] * 3)
report("C4 k = 4 equality: relabellings attain; n = 1 iff max = r; n = 2 family; strict for n = 3, 4", good, caught)

print("ALL PASS" if all(results) else "SOME CHECK FAILED")
sys.exit(0 if all(results) else 1)
