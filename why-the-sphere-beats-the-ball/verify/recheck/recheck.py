"""Independent recheck of "Why the sphere beats the ball", sharing no code with verify.py.

Monte Carlo on actual points: for several radius triples, sample independent uniform directions on concentric
spheres, test acuteness from the side lengths, and compare with the formula of Theorem 1 (within 5 standard
errors); the ball value 33/70 by simulation and by exact symbolic integration of the formula; the centre
mixture in the plane and in space by simulation. Seeded; numpy and sympy.

    timeout 900 nice -n 15 ~/.venvs/main/bin/python recheck.py
"""
from __future__ import annotations

import sys

import numpy as np
import sympy as sp

N = 2_000_000
rng = np.random.default_rng(20261010)


def directions(n: int, d: int) -> np.ndarray:
    x = rng.standard_normal((n, d))
    return x / np.linalg.norm(x, axis=1, keepdims=True)


def acute_rate(P: np.ndarray, Q: np.ndarray, R: np.ndarray) -> tuple[float, float]:
    a2 = ((Q - R) ** 2).sum(1)
    b2 = ((P - R) ** 2).sum(1)
    c2 = ((P - Q) ** 2).sum(1)
    ok = (a2 + b2 > c2) & (b2 + c2 > a2) & (c2 + a2 > b2)
    p = ok.mean()
    return p, np.sqrt(p * (1 - p) / len(ok))


def formula(a: float, b: float, c: float, k: float = 6.0) -> float:
    a, b, c = sorted((a, b, c), reverse=True)
    h = np.sqrt(max(0.0, b * b + c * c - a * a))
    return b / (2 * a) + c * c / (k * a * b) - h ** 3 / (6 * a * b * c)


def run(k: float = 6.0, ball_power: int = 2, centre: float = 0.5) -> int:
    n = 0
    for a, b, c in [(1, 1, 1), (1, 1, 0.5), (1, 0.8, 0.6), (2, 1, 1), (1, 0.9, 0.2), (3, 1, 0.5), (1.2, 1, 0.9)]:
        p, se = acute_rate(a * directions(N, 3), b * directions(N, 3), c * directions(N, 3))
        f = formula(a, b, c, k)
        assert abs(p - f) < 5 * se, (a, b, c, p, f, se)
        assert f <= 0.5 + 1e-12 and (f < 0.5 - 1e-9 or a == b)
        n += 2
        print(f"P({a},{b},{c}) simulated {p:.5f} +- {se:.5f}, formula {f:.5f}", flush=True)
    # the ball: simulation, and exact integration of the formula against the ordered radial density
    r = rng.random((3, N)) ** (1 / 3)
    p, se = acute_rate(r[0, :, None] * directions(N, 3), r[1, :, None] * directions(N, 3),
                       r[2, :, None] * directions(N, 3))
    assert abs(p - 33 / 70) < 5 * se, (p, se)
    bb, cc = sp.symbols("b c", positive=True)
    dens = 18 * bb ** ball_power * cc ** 2
    first = sp.integrate(sp.integrate(dens * (bb / 2 + cc ** 2 / (6 * bb)), (cc, 0, bb)), (bb, 0, 1))
    hh = sp.sqrt(bb ** 2 + cc ** 2 - 1)
    second = sp.integrate(sp.integrate(dens * hh ** 3 / (6 * bb * cc), (cc, sp.sqrt(1 - bb ** 2), bb)),
                          (bb, 1 / sp.sqrt(2), 1))
    assert sp.nsimplify(sp.simplify(first - second)) == sp.Rational(33, 70), (first, second)
    n += 2
    print(f"ball: simulated {p:.5f} +- {se:.5f}; exact integral of the formula {sp.simplify(first - second)}", flush=True)
    # centre mixtures
    for d, F in [(2, lambda e: (1 - e) ** 2 * (1 + 5 * e) / 4), (3, lambda e: (1 - e) ** 2 * (1 + 2 * e) / 2)]:
        for e in (0.1, 0.3):
            pts = [directions(N, d) * (rng.random(N) >= e)[:, None] for _ in range(3)]
            p, se = acute_rate(*pts)
            # one-centre triangles are acute with probability `centre`
            want = (1 - e) ** 3 * (0.25 if d == 2 else 0.5) + 3 * e * (1 - e) ** 2 * centre
            assert abs(want - F(e)) < 1e-12 and abs(p - want) < 5 * se, (d, e, p, want, se)
            n += 1
            print(f"dimension {d}, centre mass {e}: simulated {p:.5f} +- {se:.5f}, F = {F(e):.5f}", flush=True)
    return n


if __name__ == "__main__":
    print(f"positive: {run()} checks passed\n", flush=True)
    for name, kw in {"coefficient 5 for c^2/ab": dict(k=5.0), "uniform radius for the ball": dict(ball_power=0),
                     "one-centre triangle acute 1/4": dict(centre=0.25)}.items():
        try:
            run(**kw)
        except AssertionError as e:
            print(f"rejected mutant: {name} ({str(e)[:80]})\n", flush=True)
        else:
            sys.exit(f"UNDETECTED MUTANT: {name}")
    print("all 3 mutants rejected")
