"""Residue formula for P_n(q) = prod_{k<=n} (1-q^k)/(1+q^k), MSE q/5150767.

Claim (derived by hand, checked here):
  P_n has only simple poles, at primitive (2m)-th roots of unity zeta = e^{i pi j/m} with floor(n/m) = 2e+1 odd.
  Writing n = (2e+1)m + rho (0 <= rho < m), the partial-fraction coefficient
      a(zeta) = lim_{q->zeta} (1 - q/zeta) P_n(q)
  equals
      a = (2/m) * 4^e e!^2/(2e+1)! * sigma_j * prod_{k=1}^{rho} i cot(pi j k/(2m)),
      sigma_j = prod_{k=1}^{m-1} (-i tan(pi j k/(2m)))   (a unit: +-1 or +-i).
  Hence c_n(N) = [q^N] P_n = sum_zeta a(zeta) zeta^{-N} for N >= 1.
Checks: (1) c_n(N) from the residue sum equals the exact power-series coefficients;
        (2) the residue formula equals a numerical limit.
"""

from __future__ import annotations

import sys
from math import factorial, gcd

import mpmath as mp

mp.mp.dps = 40


def series(n: int, N: int) -> list[int]:
    """Exact coefficients c_n(0..N) of P_n(q)."""
    y = [0] * (N + 1)
    y[0] = 1
    for k in range(1, n + 1):
        y = [
            y[i] - (y[i - k] if i >= k else 0) for i in range(N + 1)
        ]  # times (1 - q^k)
        for i in range(k, N + 1):  # divide by (1 + q^k)
            y[i] -= y[i - k]
    return y


def poles(n: int) -> list[tuple[int, int]]:
    """(m, j): pole at e^{i pi j/m}, j a unit mod 2m."""
    return [
        (m, j)
        for m in range(1, n + 1)
        if (n // m) % 2 == 1
        for j in range(1, 2 * m)
        if gcd(j, 2 * m) == 1
    ]


def a_formula(n: int, m: int, j: int, mutant: bool = False) -> mp.mpc:
    e, rho = divmod(n - m, 2 * m)
    assert (n // m) == 2 * e + 1 and 0 <= rho < m
    C = mp.mpf(2) / m * mp.mpf(4) ** e * factorial(e) ** 2 / factorial(2 * e + 1)
    if mutant:
        C *= 2
    s = mp.mpc(1)
    for k in range(1, m):
        s *= -1j * mp.tan(mp.pi * j * k / (2 * m))
    for k in range(1, rho + 1):
        s *= 1j * mp.cot(mp.pi * j * k / (2 * m))
    return C * s


def a_numeric(n: int, m: int, j: int) -> mp.mpc:
    z = mp.expj(mp.pi * j / m)
    q = z * (1 - mp.mpf(10) ** -25)
    P = mp.mpc(1)
    for k in range(1, n + 1):
        P *= (1 - q**k) / (1 + q**k)
    return (1 - q / z) * P


def check(n: int, mutant: bool = False) -> float:
    ps = poles(n)
    N = 3 * n * n
    c = series(n, N)
    err = 0.0
    for N_ in range(1, N + 1):
        v = sum(
            a_formula(n, m, j, mutant) * mp.expj(-mp.pi * j * N_ / m) for m, j in ps
        )
        err = max(err, float(abs(v - c[N_])))
    for m, j in ps[:6]:
        err = max(
            err, float(abs(a_formula(n, m, j, mutant) - a_numeric(n, m, j))) / 1e3
        )
    return err


if __name__ == "__main__":
    bad = False
    for n in range(2, 16):
        e = check(n)
        print(f"n={n:2d} poles={len(poles(n)):3d} max err {e:.2e}")
        bad |= e > 1e-15
    em = check(7, mutant=True)
    print(
        f"mutant (C doubled) n=7 err {em:.2e} -> {'caught' if em > 1e-3 else 'MISSED'}"
    )
    bad |= em < 1e-3
    print("FAIL" if bad else "ALL PASS")
    sys.exit(int(bad))
