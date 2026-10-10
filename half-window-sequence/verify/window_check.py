"""Verify chapter 4 (MSE q/4748129): n a_n -> 1/(1 - ln 2).

Checks, each from the recurrence as stated in the question:
  1. window identity n a_n = 1 + sum_{n/2 <= k < n} a_k, exact rationals, n <= N_EXACT;
  2. positivity and monotonicity of a_n, and c_n = n a_n <= 20 (Lemma 4.3), exact;
  3. window harmonic sums: s_n <= ln 2 (n odd), s_n <= ln 2 + 1/n (n even), s_n -> ln 2;
  4. floating-point run to N_FLOAT: c_n -> A, with n (c_n - A) settling separately on odd and even n.
Run with MUTANT=1..3 to plant an error; each mutant must FAIL.
"""
from __future__ import annotations

import math
import os
import sys
from fractions import Fraction

MUTANT = int(os.environ.get("MUTANT", "0"))
N_EXACT = 3000
N_FLOAT = 2_000_001
A = 1 / (1 - math.log(2))


def step(a: list, n: int) -> object:
    if n % 2 == 0:
        return a[n - 1]
    if MUTANT == 1:
        return a[n - 1] - a[(n + 1) // 2] / n  # wrong index
    if MUTANT == 2:
        return a[n - 1] - a[(n - 1) // 2] / (n - 1)  # wrong divisor
    return a[n - 1] - a[(n - 1) // 2] / n


def window(n: int) -> range:
    lo = (n + 1) // 2 if MUTANT != 3 else n // 2 + 1  # mutant 3: drops k = n/2 for even n
    return range(lo, n)


def main() -> int:
    ok = True
    a: list = [None, Fraction(1)]
    for n in range(2, N_EXACT + 1):
        a.append(step(a, n))
    ident = all(n * a[n] == 1 + sum(a[k] for k in window(n)) for n in range(1, N_EXACT + 1))
    pos = all(a[n] > 0 and a[n] <= a[n - 1] for n in range(2, N_EXACT + 1))
    bnd = all(n * a[n] <= 20 for n in range(1, N_EXACT + 1))
    print(f"1. window identity n<={N_EXACT}: {ident}")
    print(f"2. a_n > 0, nonincreasing, c_n <= 20: {pos and bnd}")
    ok &= ident and pos and bnd

    ln2 = math.log(2)
    s_ok = True
    for n in range(2, N_EXACT + 1):
        s = float(sum(Fraction(1, k) for k in window(n)))
        cap = ln2 if n % 2 else ln2 + 1 / n
        s_ok &= s <= cap + 1e-15
    s_big = sum(1 / k for k in window(10**6 + 1))
    print(f"3. window sums bounded: {s_ok}; s_(1e6+1) - ln2 = {s_big - ln2:.2e}")
    ok &= s_ok and abs(s_big - ln2) < 1e-6

    f = [0.0] * (N_FLOAT + 1)
    f[1] = 1.0
    for n in range(2, N_FLOAT + 1):
        f[n] = step(f, n)
    for n in (10**4, 10**5, 10**6, 2 * 10**6):
        print(f"   n={n}: n(c_n-A) even {n * (n * f[n] - A):+.5f}, odd {(n + 1) * ((n + 1) * f[n + 1] - A):+.5f}")
    top = max(n * f[n] for n in range(1, N_FLOAT + 1))
    lim = abs(N_FLOAT * f[N_FLOAT] - A)
    print(f"4. max c_n = {top:.9f} (A = {A:.9f}); |c_N - A| = {lim:.2e}")
    ok &= lim < 1e-5 and top < A

    print("PASS" if ok else "FAIL")
    return 0 if ok else 1


if __name__ == "__main__":
    sys.exit(main())
