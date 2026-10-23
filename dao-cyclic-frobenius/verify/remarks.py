"""Counts quoted in Remarks 1 and 2 (minimality and pseudo-Frobenius sets). Run: python3 -I remarks.py"""
import itertools
import math
import random
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
from verify_note import generators, membership


def in_semigroup(v: int, gens: list[int]) -> bool:
    return membership(gens, v)[v]


def minimal(xs: list[int]) -> bool:
    return all(x not in xs[:i] + xs[i + 1:] and not in_semigroup(x, xs[:i] + xs[i + 1:]) for i, x in enumerate(xs))


def remark1_exhaustive() -> tuple[int, int]:
    tot = bad = 0
    for n in (2, 3, 4, 5):
        for a in itertools.product(range(1, 9 if n < 4 else 6), repeat=n):
            xs = generators(list(a))
            if math.gcd(*xs) != 1:
                continue
            tot += 1
            bad += not minimal(xs)
    return tot, bad


def remark1_random() -> tuple[int, int]:
    random.seed(1)
    tot = bad = 0
    for _ in range(20000):
        n = random.randint(2, 7)
        a = [random.choice([1, 1, 1, 2, 2, 3, 4, 5, 7]) for _ in range(n)]
        xs = generators(a)
        if math.gcd(*xs) != 1 or max(xs) > 20000:
            continue
        tot += 1
        bad += not minimal(xs)
    return tot, bad


def remark2() -> tuple[int, int]:
    random.seed(2)
    tot = ok = 0
    for _ in range(3000):
        n = random.randint(2, 5)
        a = [random.choice([1, 1, 2, 2, 3, 4, 5]) for _ in range(n)]
        xs = generators(a)
        if math.gcd(*xs) != 1 or max(xs) > 400:
            continue
        N = math.prod(a) - 1
        F = (n - 1) * N
        rep = membership(xs, F + 2 * max(xs) + 5)
        pf = [f for f in range(1, F + 1) if not rep[f] and all(rep[f + x] for x in xs)]
        tot += 1
        ok += pf == [k * N for k in range(1, n)]
    return tot, ok


if __name__ == "__main__":
    t1, b1 = remark1_exhaustive()
    t2, b2 = remark1_random()
    t3, o3 = remark2()
    print(f"Remark 1 exhaustive: {t1} coprime lists, {b1} non-minimal")
    print(f"Remark 1 random: {t2} coprime lists, {b2} non-minimal")
    print(f"Remark 2: {o3} of {t3} have PF = {{N, ..., (n-1)N}}")
    good = (t1, b1, t2, b2, t3, o3) == (3703, 0, 14459, 0, 2186, 2186)
    print("ALL PASS" if good else "FAILED")
