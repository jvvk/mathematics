"""Theorem A of the paper (PROOF_static.md): near the notch-60 lattice front with m downs and n ups (m, n >= 2,
n/2 < m < 2n), the first disk is a pentagon when, along (alpha, sigma, eps, c) = t (a, s, e, -q),

    window:    (e - a)/2 - q k_u  <  s  <  e - q (sqrt3 sin u + 5 cos u)/4,
    validity:  s > -(q/2) k_u,   a + s - e > (q/2) k_u,          k_u = cos(u - 60 deg) = sin(u + 30 deg),

u = bearing of the up vectors, tan u = sqrt3 m / (2n - m). Front H: hinge 180 + alpha between the last two downs
(at A), notch hinge 60 + sigma (at B), hinge 180 - eps between the first two ups (at C), every other hinge at its
lattice value except the ridge, which takes up the difference (300 - (alpha + sigma - eps)); every disk (seeds
included) of diameter 1 + c y.

Part 1: the universal clearances of the pentagon apex (touching A and E) against exact nonlinear geometry, for
several (m, n) and random deviation directions: (exact - linear)/t -> 0.
Part 2: validity of the initial front, checked directly (no two disks overlap), and the independent simulator
against the window on valid fronts: rays inside, just inside, and on both sides of the window.
"""

from __future__ import annotations

import math
import os
import random
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from independent_stack import Stack


def bearing_u(m: int, n: int) -> float:
    return math.atan2(math.sqrt(3) * m, 2 * n - m)


def build(m: int, n: int, alpha: float, sigma: float, eps: float, cc: float):
    """Front D^m U^n with consistent seeds: disks (x, y, d), the disks Z, A, B, C, E, and the circumference."""
    u = bearing_u(m, n)
    bD = u - 2 * math.pi / 3
    rel = (
        [alpha] * (m - 1)
        + [0.0]
        + [2 * math.pi / 3 - sigma, 2 * math.pi / 3 - sigma + eps]
    )
    rel += [2 * math.pi / 3 - sigma + eps] * (n - 2)
    N = m + n
    phi, ys = 0.0, [0.0] * N
    for _ in range(100):
        Ls = [1 + cc * (ys[k] + ys[(k + 1) % N]) / 2 for k in range(N)]
        for _ in range(50):
            f = sum(Ls[k] * math.sin(bD + phi + rel[k]) for k in range(N))
            g = sum(Ls[k] * math.cos(bD + phi + rel[k]) for k in range(N))
            phi -= f / g
        pts = [(0.0, 0.0)]
        for k in range(N - 1):
            a = bD + phi + rel[k]
            pts.append(
                (pts[-1][0] + Ls[k] * math.cos(a), pts[-1][1] + Ls[k] * math.sin(a))
            )
        ys = [p[1] for p in pts]
    lam = sum(Ls[k] * math.cos(bD + phi + rel[k]) for k in range(N))
    disks = [(x, y, 1 + cc * y) for x, y in pts]
    idx = {"Z": m - 2, "A": m - 1, "B": m, "C": m + 1, "E": m + 2}
    def disk(i: int) -> tuple[float, float, float]:
        x, y, d = disks[i % N]
        return (x + lam * (i // N), y, d)

    return disks, {k: disk(i) for k, i in idx.items()}, lam


def window(m: int, n: int, alpha: float, eps: float, cc: float) -> tuple[float, float]:
    u = bearing_u(m, n)
    lo = (eps - alpha) / 2 - abs(cc) * math.sin(u + math.pi / 6)
    hi = eps - abs(cc) * (math.sqrt(3) * math.sin(u) + 5 * math.cos(u)) / 4
    return lo, hi


def linear_slacks(
    m: int, n: int, alpha: float, sigma: float, eps: float, cc: float
) -> dict[str, float]:
    u = bearing_u(m, n)
    s3 = math.sqrt(3)
    return {
        "C": s3 / 2 * (eps - sigma) + cc * (3 * math.sin(u) + 5 * s3 * math.cos(u)) / 8,
        "Z": s3 / 2 * (2 * sigma + alpha - eps)
        - cc * (3 * math.sin(u) + s3 * math.cos(u)) / 2,
    }


def exact_slacks(
    m: int, n: int, alpha: float, sigma: float, eps: float, cc: float
) -> dict[str, float]:
    """Apex touching A and E with the diameter law (height origin where d = 1), clearances to Z and C."""
    _, F, _ = build(m, n, alpha, sigma, eps, cc)
    S = Stack([], 1.0, cc)
    q = S.apex(F["A"], F["E"])
    return {
        k: math.hypot(q[0] - F[k][0], q[1] - F[k][1]) - (q[2] + F[k][2]) / 2
        for k in ("C", "Z")
    }


def valid(m: int, n: int, alpha: float, sigma: float, eps: float, cc: float) -> bool:
    """No two disks of the initial front overlap (all pairs except the touching neighbours, all images)."""
    disks, _, lam = build(m, n, alpha, sigma, eps, cc)
    N = len(disks)
    for i in range(N):
        for j in range(N):
            for sh in (-1, 0, 1):
                if (i == j and sh == 0) or (j == i + 1 and sh == 0) or (i == N - 1 and j == 0 and sh == 1):
                    continue
                if (j == i - 1 and sh == 0) or (i == 0 and j == N - 1 and sh == -1):
                    continue
                xj = disks[j][0] + sh * lam
                d = math.hypot(xj - disks[i][0], disks[j][1] - disks[i][1])
                if d < (disks[i][2] + disks[j][2]) / 2 - 1e-12:
                    return False
    return True


def first_event(m: int, n: int, alpha: float, sigma: float, eps: float, cc: float) -> str:
    disks, _, lam = build(m, n, alpha, sigma, eps, cc)
    S = Stack([(x / lam, y / lam, d / lam) for x, y, d in disks], 1 / lam, cc, tol=1e-13)
    p0 = S.parastichy()
    dl = S.step()
    return f"{ {1: 'T', 0: 'R', -1: 'P'}.get(dl, dl) } {p0}->{S.parastichy()}"


if __name__ == "__main__":
    random.seed(7)
    print(
        "Part 1: (exact - linear)/t for the clearances of the pentagon apex (t = 1e-4)"
    )
    worst = 0.0
    for m, n in ((2, 2), (2, 3), (3, 2), (3, 4), (4, 7), (5, 3), (6, 11)):
        for _ in range(3):
            d = [random.uniform(-1, 1) for _ in range(4)]
            t = 1e-4
            p = [t * v for v in d]
            ex, li = exact_slacks(m, n, *p), linear_slacks(m, n, *p)
            err = max(abs(ex[k] - li[k]) / t for k in ex)
            worst = max(worst, err)
        print(f"  (m,n)=({m},{n}): max |exact-linear|/t = {err:.1e}")
    assert worst < 2e-3, worst
    print(f"Part 1 passed (worst {worst:.1e})")

    print(
        "\nPart 2: simulator vs the window, rays (alpha, eps, c) with sigma placed relative to the window"
    )
    t = 2e-3
    bad = tested = skipped = 0
    for m in range(2, 7):
        for n in range(2, 2 * m):
            if not (n < 2 * m and m < 2 * n):
                continue
            row = []
            for alpha, cc in ((0.0, 0.0), (0.6 * t, -0.1 * t), (1.0 * t, -0.3 * t)):
                lo, hi = window(m, n, alpha, t, cc)
                for where, sig in (
                    ("mid", (lo + hi) / 2),
                    ("in-hi", hi - 0.1 * (hi - lo)),
                    ("above", hi + 0.15 * t),
                    ("below", lo - 0.15 * t),
                ):
                    if not valid(m, n, alpha, sig, t, cc):
                        skipped += 1
                        row.append(f"{where}:-")
                        continue
                    ev = first_event(m, n, alpha, sig, t, cc)
                    ok = ev.startswith("P") == (where not in ("above", "below"))
                    bad += not ok
                    tested += 1
                    row.append(f"{where}:{ev[0]}{'' if ok else '!'}")
            print(f"  ({m},{n}) " + " ".join(row))
    print(f"valid fronts tested: {tested}, invalid fronts skipped ('-'): {skipped}, mismatches: {bad}")
    assert bad == 0
