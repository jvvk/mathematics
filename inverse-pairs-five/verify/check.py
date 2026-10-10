"""Inverse pairs (MSE 5146740): numerical checks of every lemma, independent of the Lean proof.

    python3 check.py            # prints PASS
    MUTANT=1 python3 check.py   # inverses off by one in one residue class: must print FAIL
    MUTANT=2 python3 check.py   # full-grid sum divided by p - 1 instead of p: must print FAIL
    MUTANT=3 python3 check.py   # staircase error without the column width h: must print FAIL

Inverses come from the recurrence abar = -(p // a) * (p mod a)bar (mod p), a different method from
sums.c (extended Euclid); `cc` is used to compile sums.c and the two are compared.
1. S(p) and C(p) against sums.c for p near 10^3 .. 10^6.
2. Lemma 1: |N(I, J) - |I||J|/p| <= 3 sqrt(p) (1 + ln p)^2 on random and extreme intervals.
3. Lemma 2: |Rc(X) - Tc(X)/p| <= L E1 + h with L = ceil(p^(1/4)), h = ceil(p^(3/4)), over X in [1, p^2].
4. Lemma 3: R(m) <= sum_{1 <= k <= m/p} d(1 + kp), exactly.
5. The layer-cake identity S - C - 1 = sum_m (w(m) - w(m+1)) (R(m) - Tc(m)/p) - w(N+1)/p, N = (p-1)^2.
6. |C(p) - 4| <= 8/sqrt(p).
"""
from __future__ import annotations

import math
import os
import random
import re
import subprocess
import sys
import tempfile
from pathlib import Path

MUTANT = os.environ.get("MUTANT", "")
HERE = Path(__file__).resolve().parent


def inverses(p: int) -> list[int]:
    inv = [0, 1] + [0] * (p - 2)
    for a in range(2, p):
        inv[a] = (-(p // a) * inv[p % a]) % p
    if MUTANT == "1":
        inv[2] = inv[2] % (p - 1) + 1  # planted error
    return inv


def S(p: int, inv: list[int]) -> float:
    return math.fsum(1 / math.sqrt(a * inv[a]) for a in range(1, p))


def C(p: int) -> float:
    h = math.fsum(1 / math.sqrt(a) for a in range(1, p))
    return h * h / (p - 1 if MUTANT == "2" else p)


def is_prime(n: int) -> bool:
    return n > 1 and all(n % d for d in range(2, math.isqrt(n) + 1))


def next_prime(n: int) -> int:
    while not is_prime(n):
        n += 1
    return n


def E1(p: int) -> float:
    return 3 * math.sqrt(p) * (1 + math.log(p)) ** 2


def box_count(inv: list[int], a0: int, L: int, b0: int, M: int) -> int:
    return sum(1 for a in range(a0, a0 + L) if b0 <= inv[a] < b0 + M)


def check_sums() -> bool:
    ps = [next_prime(n) for n in (1000, 10000, 100000, 1000000)]
    with tempfile.TemporaryDirectory() as tmp:
        exe = Path(tmp) / "sums"
        subprocess.run(["cc", "-O2", "-o", str(exe), str(HERE / "sums.c"), "-lm"], check=True)
        out = subprocess.run([str(exe), *map(str, ps)], capture_output=True, text=True,
                             check=True).stdout
    ok = True
    for line in out.strip().splitlines():
        p = int(re.search(r"p=(\d+)", line).group(1))
        s_c = float(re.search(r"S=([\d.]+)", line).group(1))
        c_c = float(re.search(r" C=([\d.]+)", line).group(1))
        inv = inverses(p)
        ok &= abs(S(p, inv) - s_c) < 1e-9 and abs(C(p) - c_c) < 1e-9
    print(f"1. S(p), C(p) agree with sums.c for p = {ps}: {ok}")
    return ok


def check_rect() -> bool:
    rng = random.Random(5146740)
    worst = 0.0
    for p in (101, 1009, 10007):
        inv = inverses(p)
        boxes = [(1, p - 1, 1, p - 1), (1, 1, 1, p - 1), (1, (p - 1) // 2, 1, (p - 1) // 2)]
        for _ in range(60):
            a0 = rng.randint(1, p - 1); L = rng.randint(0, p - a0)
            b0 = rng.randint(1, p - 1); M = rng.randint(0, p - b0)
            boxes.append((a0, L, b0, M))
        for a0, L, b0, M in boxes:
            worst = max(worst, abs(box_count(inv, a0, L, b0, M) - L * M / p) / E1(p))
    ok = worst <= 1
    print(f"2. Lemma 1: worst |N - |I||J|/p| / E1 = {worst:.4f}: {ok}")
    return ok


def counts(p: int, inv: list[int]) -> tuple[list[int], list[int]]:
    """Rc(X) and Tc(X) for X = 0 .. (p-1)^2."""
    N = (p - 1) ** 2
    hist = [0] * (N + 2)
    for a in range(1, p):
        hist[a * inv[a]] += 1
    Rc, run = [0] * (N + 1), 0
    for X in range(N + 1):
        run += hist[X]
        Rc[X] = run
    Tc = [sum(min(p - 1, X // a) for a in range(1, p)) for X in range(N + 1)]
    return Rc, Tc


def check_stair() -> bool:
    ok, worst = True, 0.0
    for p in (101, 211, 401):
        inv = inverses(p)
        Rc, Tc = counts(p, inv)
        L, h = math.ceil(p ** 0.25), math.ceil(p ** 0.75)
        col = 0 if MUTANT == "3" else h
        bound = L * E1(p) + col
        for X in range(1, (p - 1) ** 2 + 1):
            dev = abs(Rc[X] - Tc[X] / p)
            worst = max(worst, dev / bound)
            ok &= dev <= bound
        # the squeeze without Weil: the two staircases of all pairs differ by at most h (p - 1)
        edges = [min(1 + l * h, p) for l in range(L + 1)]
        for X in range(1, (p - 1) ** 2 + 1, 37):
            up = sum((edges[l + 1] - edges[l]) * min(p - 1, X // edges[l]) for l in range(L))
            lo = sum((edges[l + 1] - edges[l]) * min(p - 1, X // max(edges[l + 1] - 1, 1))
                     for l in range(L))
            ok &= up - lo <= col * (p - 1)
    print(f"3. Lemma 2: worst |Rc - Tc/p| / (L E1 + h) = {worst:.4f}; staircase gap <= h(p-1): {ok}")
    return ok


def ndiv(n: int) -> int:
    return sum(2 - (d * d == n) for d in range(1, math.isqrt(n) + 1) if n % d == 0)


def check_small() -> bool:
    ok = True
    for p in (101, 211, 1009):
        inv = inverses(p)
        for m in (p, 2 * p, 5 * p + 3, p * p // 7, (p - 1) ** 2):
            R = sum(1 for a in range(2, p) if a * inv[a] <= m)
            ok &= R <= sum(ndiv(1 + k * p) for k in range(1, m // p + 1))
    print(f"4. Lemma 3: R(m) <= sum d(1 + kp): {ok}")
    return ok


def check_identity() -> bool:
    ok, worst = True, 0.0
    for p in (101, 211, 401):
        inv = inverses(p)
        Rc, Tc = counts(p, inv)
        N = (p - 1) ** 2
        w = lambda m: 1 / math.sqrt(m)
        rhs = math.fsum((w(m) - w(m + 1)) * ((Rc[m] - 1) - Tc[m] / p) for m in range(1, N + 1)) \
            - w(N + 1) / p
        lhs = S(p, inv) - C(p) - 1
        worst = max(worst, abs(lhs - rhs))
    ok = worst < 1e-9
    print(f"5. layer-cake identity: worst error {worst:.2e}: {ok}")
    return ok


def check_C() -> bool:
    ok = all(abs(C(p) - 4) <= 8 / math.sqrt(p) for p in range(2, 3000) if is_prime(p))
    print(f"6. |C(p) - 4| <= 8/sqrt(p) for primes p < 3000: {ok}")
    return ok


def main() -> int:
    results = [check_sums(), check_rect(), check_stair(), check_small(), check_identity(),
               check_C()]
    print("PASS" if all(results) else "FAIL")
    return 0 if all(results) else 1


if __name__ == "__main__":
    sys.exit(main())
