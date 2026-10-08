"""Checks for Lemma 3, Theorem 4 and the consequences. Illustrations of the proofs, not replacements for them.

1. Lemma 3: E X^2, E X^4 of X = alpha cos U + beta cos V, exactly over rational weights.
2. Theorem 4, case analysis: over a rational grid of (a, b, D, mu), the weight sets {|1+mu| b, |mu| a} and
   {b, |mu| D} agree exactly when mu = 0, or D = a + b and mu = b/a.
3. Direct simulation of the configuration (two-sample Kolmogorov-Smirnov on distances): the laws agree in
   cases (1) and (2), for Dan's ratios r = 0.4, 1, 2, and in the mirror case; they differ for separated
   circles at the case (2) ratio, off the axis, and for a = b = 1, c = 2.
4. Equal-radius corollary: the one-integral form against Dan's closed form at 60-digit precision (agreement to 40 digits).

Run: python check_theorem.py            (expect PASS)
     python check_theorem.py --mutant M  (M in moment, case, gp, constant; expect AssertionError)
"""

import sys
from fractions import Fraction as F
from itertools import product

import mpmath as mp
import numpy as np

MUTANT = sys.argv[2] if len(sys.argv) > 2 and sys.argv[1] == "--mutant" else None
N = 200_000
KS_SAME = 0.008  # 5% critical value for n = m = 2e5 is about 0.0043
KS_DIFF = 0.012


def check_moments() -> None:
    # E cos^2 = 1/2, E cos^4 = 3/8, odd moments vanish; expand (alpha c + beta d)^k termwise.
    m = {0: F(1), 1: F(0), 2: F(1, 2), 3: F(0), 4: F(3, 8)}
    binom = {2: [1, 2, 1], 4: [1, 4, 6, 4, 1]}
    vals = [F(-2), F(-1, 3), F(0), F(1, 2), F(1), F(5, 3)]
    for al, be in product(vals, repeat=2):
        ex = {
            k: sum(
                binom[k][j] * al**j * be ** (k - j) * m[j] * m[k - j]
                for j in range(k + 1)
            )
            for k in (2, 4)
        }
        s, p = al**2 + be**2, al**2 * be**2
        # The paper uses only E X^2 (with the support endpoint); E X^4 is an extra check. The mutant hits E X^2.
        c2 = F(1, 2) if MUTANT != "moment" else F(1, 3)
        assert ex[2] == c2 * s and ex[4] == F(3, 8) * s**2 + F(3, 4) * p, (al, be)
    print(f"Lemma 3 moments: exact for {len(vals) ** 2} weight pairs")


def check_cases() -> None:
    grid = [F(1, 3), F(1, 2), F(1), F(3, 2), F(2)]
    hits = 0
    for a, b in product(grid, repeat=2):
        for D in (a + b, a + b + F(1, 4), a + b + 1):
            for mu in sorted({F(0), b / a, -b / a, F(-2), F(1), F(-1, 2), F(3), a / b}):
                same = sorted([(1 + mu) ** 2 * b**2, mu**2 * a**2]) == sorted(
                    [b**2, mu**2 * D**2]
                )
                claim = mu == 0 or (D == a + b and mu == b / a)
                if MUTANT == "case":
                    claim = mu == 0 or mu == b / a
                assert same == claim, (a, b, D, mu)
                hits += same
    print(
        f"Theorem 4 case analysis: exact over the grid, {hits} equal-law configurations, all of form (1) or (2)"
    )


def unit(t: np.ndarray) -> np.ndarray:
    return np.stack([np.cos(t), np.sin(t)], axis=-1)


def line_distance(X: np.ndarray, Y: np.ndarray, O: np.ndarray) -> np.ndarray:
    d = Y - X
    return np.abs(d[:, 0] * (O[1] - X[:, 1]) - d[:, 1] * (O[0] - X[:, 0])) / np.hypot(
        d[:, 0], d[:, 1]
    )


def ks(x: np.ndarray, y: np.ndarray) -> float:
    grid = np.sort(np.concatenate([x, y]))
    fx = np.searchsorted(np.sort(x), grid, side="right") / len(x)
    fy = np.searchsorted(np.sort(y), grid, side="right") / len(y)
    return float(np.max(np.abs(fx - fy)))


def distances(
    a: float, b: float, D: float, O: tuple[float, float], rng: np.random.Generator
) -> dict[str, np.ndarray]:
    """P = (-D, 0) radius a, Q = (0, 0) radius b. Returns d(O, AB), d(O, BC), d(O, AA') and the predicted law."""
    P, Q, Ov = np.array([-D, 0.0]), np.zeros(2), np.array(O)
    A, A2 = (P + a * unit(rng.uniform(0, 2 * np.pi, N)) for _ in range(2))
    B, C = (Q + b * unit(rng.uniform(0, 2 * np.pi, N)) for _ in range(2))
    U, V = rng.uniform(0, 2 * np.pi, (2, N))
    law = np.abs(b * np.cos(U) - np.hypot(*Ov) * np.cos(V))
    return {
        "AB": line_distance(A, B, Ov),
        "BC": line_distance(B, C, Ov),
        "AA": line_distance(A, A2, Ov),
        "law": law,
    }


def check_simulation() -> None:
    rng = np.random.default_rng(499477)
    same = []
    for r in (0.4, 1.0, 2.0):  # Dan: radii 1/r, 1, r touching; O at distance 1 + r
        c = r * (1.5 if MUTANT == "gp" else 1)
        same.append(
            (f"Dan r={r}", distances(1 / r, 1, 1 / r + 1, (1 + c, 0), rng), "BC")
        )
    a, b = 0.5, 1.0
    same.append(
        ("case (1), separated", distances(a, b, a + b + 0.5, (0, 0), rng), "BC")
    )
    same.append(
        ("case (2), a=1/2", distances(a, b, a + b, (b * (a + b) / a, 0), rng), "BC")
    )
    same.append(
        (
            "mirror, O beyond P",
            distances(a, b, a + b, (-(a + b) - a * (a + b) / b, 0), rng),
            "AA",
        )
    )
    for name, d, other in same:
        k = ks(d["AB"], d[other])
        print(f"  {name}: KS(AB,{other})={k:.4f}")
        assert k < KS_SAME, name
        if other == "BC":
            assert ks(d["AB"], d["law"]) < KS_SAME, name
    differ = [
        (
            "separated at case (2) ratio",
            distances(a, b, a + b + 0.5, (b * (a + b + 0.5) / a, 0), rng),
        ),
        ("off axis by 0.3", distances(a, b, a + b, (b * (a + b) / a, 0.3), rng)),
        ("a=b=1, c=2", distances(1, 1, 2, (3, 0), rng)),
    ]
    for name, d in differ:
        k = ks(d["AB"], d["BC"])
        print(f"  {name}: KS(AB,BC)={k:.4f}  (must differ)")
        assert k > KS_DIFF, name
    d = differ[-1][1]
    print(
        f"  a=b=1, c=2 hit probabilities: AB {np.mean(d['AB'] < 2):.3f}, BC {np.mean(d['BC'] < 2):.3f}"
    )
    d = same[2][1]
    print(
        f"  radii 1/2, 1, 2 hit probabilities: AB {np.mean(d['AB'] < 2):.4f}, BC {np.mean(d['BC'] < 2):.4f}"
    )


def check_constant() -> None:
    mp.mp.dps = 60
    one = 2 / mp.pi**2 * mp.quad(lambda v: mp.acos(2 * mp.cos(v) - 1), [0, mp.pi / 2])
    k = 2 if MUTANT == "constant" else 3
    dan = mp.mpf(3) / 4 - 2 / mp.pi**2 * (
        mp.mpf(3) / 8 * mp.log(2) ** 2
        + mp.polylog(2, -mp.sqrt(2))
        + k * mp.polylog(2, 1 / mp.sqrt(2))
    )
    print(
        f"Equal-radius corollary: integral = {mp.nstr(one, 45)}; |integral - Dan| = {mp.nstr(abs(one - dan), 3)}"
    )
    assert abs(one - dan) < mp.mpf(10) ** -40


check_moments()
check_cases()
print("simulation, n = 2e5 per sample:")
check_simulation()
check_constant()
print("PASS")
