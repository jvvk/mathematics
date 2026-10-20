"""Check of the lattice-order step in the proof of Theorem (pentagon on the first disk).

Front of the notch-60 lattice: vertices (x, 0), 0 <= x <= m, then (m, y), 0 <= y <= n, repeated with period
(m, n), in coordinates z = x D + y U. Claim: among lattice points strictly above the front polyline (in the
plane), the lowest are (m - 1, 1) + k (m, n), and every other one is higher by at least min(delta, upsilon),
where delta = |Im D| and upsilon = Im U. Checked by brute force in the plane, not via the staircase formula.
"""

from __future__ import annotations

import cmath
import math


def check(m: int, n: int) -> None:
    u = math.atan2(math.sqrt(3) * m, 2 * n - m)
    U, D = cmath.exp(1j * u), cmath.exp(1j * (u - 2 * math.pi / 3))
    P = m * D + n * U
    assert abs(P.imag) < 1e-12 and P.real > 0
    verts = [x * D for x in range(m)] + [m * D + y * U for y in range(n)]
    poly = [v + k * P for k in range(-3, 4) for v in verts]
    poly.sort(key=lambda z: z.real)

    def above(z: complex) -> bool:
        for a, b in zip(poly, poly[1:]):
            if a.real <= z.real <= b.real:
                return z.imag > a.imag + (b.imag - a.imag) * (z.real - a.real) / (b.real - a.real) + 1e-9
        raise ValueError

    pts = []
    for x in range(-4 * m, 4 * m):
        for y in range(-4 * n, 4 * n):
            z = x * D + y * U
            if 0 <= z.real < P.real - 1e-12 and above(z):
                pts.append((z.imag, x, y))
    pts.sort()
    q0 = (m - 1) * D + U
    lowest = pts[0]
    assert abs(lowest[0] - q0.imag) < 1e-9
    gap = pts[1][0] - pts[0][0]
    hmin = min(abs(D.imag), U.imag)
    assert gap >= hmin - 1e-9, (m, n, gap, hmin)
    # the lowest site is (m-1, 1) up to the period
    x, y = lowest[1], lowest[2]
    k = round((y - 1) / n)
    assert (x, y) == (m - 1 + k * m, 1 + k * n), (m, n, x, y)
    print(f"(m,n)=({m},{n}): lowest above front = (m-1,1), next gap {gap:.4f} >= min(delta,upsilon) = {hmin:.4f}")


if __name__ == "__main__":
    count = 0
    for m in range(2, 9):
        for n in range(2, 17):
            if n / 2 < m < 2 * n:
                check(m, n)
                count += 1
    print(f"all {count} shapes pass")
