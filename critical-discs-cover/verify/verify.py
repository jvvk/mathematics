"""MO 458793: is the unit disk covered by uniform-centred disks of area pi/n (radius r_n = c^{1/2}/sqrt(n), c = 1)?

Interior: Zhou (arXiv 2609.02156) criterion on a torus of area pi: covered iff int exp(H) dm = inf,
  H(t) = sum_n u_n(t), u_n(t) = m(B(0,r_n) cap B(t,r_n)) = (c/n) psi(t/r_n), psi = normalised lens area.
  Claim: H(t) - 2c ln(1/t) is bounded; printed: H - 2 ln(1/t) as t -> 0, so int exp(H) t dt diverges iff c >= 1.
Rim: Shepp in the form int_0 exp(F(t)) dt = inf, F(t) = sum_n (ell_n - t)^+, ell_n = arc fraction cut on the unit
  circle by disk n. Claim: E F(t) - c ln(1/t) is bounded; printed: EF - ln(1/t), so diverges iff c >= 1.
Prints the two differences over t = 10^-1 .. 10^-3.5; they must level off for c = 1 and drift for the mutant c = 0.9.
Usage: verify.py [c]"""

import sys

import numpy as np

C = float(sys.argv[1]) if len(sys.argv) > 1 else 1.0


def psi(s: np.ndarray) -> np.ndarray:
    s = np.clip(s, 0, 2)
    return (2 * np.arccos(s / 2) - (s / 2) * np.sqrt(4 - s * s)) / np.pi


def H(t: float, N: int) -> float:
    n = np.arange(1, N + 1, dtype=float)
    r = np.sqrt(C / n)
    return float(np.sum((C / n) * psi(t / r)))  # terms vanish once 2 r_n < t


GL_X, GL_W = np.polynomial.legendre.leggauss(400)


def E_excess(r: float, t: float) -> float:
    """E (ell - t)^+ for a disk of radius r < 1 centred uniformly in the unit disk; density of rho is 2 rho."""
    a, b = 1 - r, 1.0
    rho = (b - a) / 2 * GL_X + (a + b) / 2
    w = (b - a) / 2 * GL_W
    cosphi = np.clip((1 + rho**2 - r * r) / (2 * rho), -1, 1)
    ell = np.arccos(cosphi) / np.pi
    return float(np.sum(w * 2 * rho * np.maximum(ell - t, 0)))


def EF(t: float) -> float:
    tot, n = 0.0, 1
    while True:
        r = np.sqrt(C / n)
        if r < 1:
            if (
                r / 2 < t
            ):  # ell <= arcsin(r)/pi... bounded by r/2 for r < 1, so the rest vanish
                break
            tot += E_excess(r, t)
        n += 1
    return tot


if __name__ == "__main__":
    print(f"c = {C}")
    print(f"{'t':>10} {'H(t)-2 ln(1/t)':>18} {'EF(t)-ln(1/t)':>18}")
    hs, fs = [], []
    for e in np.arange(1, 3.51, 0.5):
        t = 10.0**-e
        N = int(4 * C / t**2) + 10
        h, f = H(t, N) - 2 * np.log(1 / t), EF(t) - np.log(1 / t)
        hs.append(h)
        fs.append(f)
        print(f"{t:10.2e} {h:18.6f} {f:18.6f}", flush=True)
    # levelling off: over the last two half-decades both differences move by less than 0.06
    flat = max(hs[-3:]) - min(hs[-3:]) < 0.06 and max(fs[-3:]) - min(fs[-3:]) < 0.06
    print("LEVELS OFF" if flat else "DRIFTS")
    sys.exit(0 if flat else 1)
