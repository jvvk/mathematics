"""Record local_existence_fit.out (Section 8): kappa2(beta_D) = (theta* - cushion)/|c| from the local pentagon
boundary of local_existence.py, over beta_D in [-105, -60] degrees, and its least-squares fit by 1, cos, sin (and
with cos 2, sin 2 added). The fitted coefficients -0.25 and -1.29904 of cos(beta_D) and sin(beta_D) are those quoted
in the paper (five-term fit). Exits nonzero if they differ by more than 1e-4 or the residual exceeds 1e-9.
Run: python3 local_existence_fit.py   (about a minute)
"""
from __future__ import annotations
import math, os, sys
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from local_existence import boundary

ANGLES = (-60.0, -65.0, -70.0, -75.0, -80.0, -83.5, -86.0, -90.0, -95.0, -100.0, -105.0)


def solve(A: list[list[float]], y: list[float]) -> tuple[list[float], float]:
    """Least squares by normal equations and Gaussian elimination; returns coefficients and max residual."""
    n = len(A[0])
    M = [[sum(r[i] * r[j] for r in A) for j in range(n)] + [sum(r[i] * v for r, v in zip(A, y))] for i in range(n)]
    for i in range(n):
        p = max(range(i, n), key=lambda k: abs(M[k][i])); M[i], M[p] = M[p], M[i]
        for k in range(n):
            if k != i:
                f = M[k][i] / M[i][i]
                M[k] = [a - f * b for a, b in zip(M[k], M[i])]
    x = [M[i][n] / M[i][i] for i in range(n)]
    return x, max(abs(sum(a * b for a, b in zip(r, x)) - v) for r, v in zip(A, y))


def main() -> int:
    b0, c = 0.06, -0.00025
    ks = []
    for deg in ANGLES:
        bd = math.radians(deg)
        k = (boundary(bd, 0.0, b0, c) - 0.0) / abs(c)
        ks.append(k)
        print(f"  {deg:6.1f} {k:.6f}")
    A1 = [[1.0, math.cos(math.radians(d)), math.sin(math.radians(d))] for d in ANGLES]
    A2 = [r + [math.cos(2 * math.radians(d)), math.sin(2 * math.radians(d))] for r, d in zip(A1, ANGLES)]
    x1, r1 = solve(A1, ks); x2, r2 = solve(A2, ks)
    print("1,cos,sin coef", [f"{v:.5f}" for v in x1], f"max resid {r1:.2e}")
    print("1,cos,sin,cos2,sin2 coef", [f"{v:.5f}" for v in x2], f"max resid {r2:.2e}")
    # the paper quotes the five-term fit: cos and sin coefficients -0.25000 and -1.29904, residual below 1e-9
    ok = abs(x2[1] + 0.25) < 1e-4 and abs(x2[2] + 1.29904) < 1e-4 and r2 < 1e-9
    print("PASS five-term fit: coefficients -0.25000, -1.29904, residual < 1e-9" if ok
          else "FAIL five-term fit differs from the paper")
    return 0 if ok else 1


if __name__ == "__main__":
    sys.exit(main())
