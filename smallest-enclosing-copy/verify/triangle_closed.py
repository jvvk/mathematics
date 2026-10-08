"""Closed form for triangles: P = (1/(2 sum L^2)) sum_k L_k^2 g(x_i, x_j), x_i = (L_i/L_k)^2,
g(al, be) = E[(1 - (al U1 + be U2)^2)_+], U uniform on [-1,1] (1-D integral against the trapezoid density).
Checks against triangle_exact.py, then scans shapes on a fine grid (law of sines: L proportional to sin(angle))."""
import math, numpy as np
def g(al, be, n=4001):
    lo, hi = abs(al - be), al + be                 # density of W = al U1 + be U2 on [-hi, hi]: trapezoid
    w = np.linspace(0, min(1.0, hi), n)
    dens = np.where(w <= lo, 1 / (2 * max(al, be)), (hi - w) / (4 * al * be))
    return 2 * np.trapezoid((1 - w ** 2) * dens, w)
def P_closed(A, B):
    ang = np.radians([A, B, 180 - A - B]); L = np.sin(ang); tot = 0.0
    for k in range(3):
        i, j = [q for q in range(3) if q != k]; tot += L[k] ** 2 * g((L[i] / L[k]) ** 2, (L[j] / L[k]) ** 2)
    return tot / (2 * (L ** 2).sum())
if __name__ == "__main__":
    from triangle_exact import P_angles
    for A, B in [(60, 60), (30, 60), (20, 40), (80, 60), (45, 45)]:
        print(A, B, round(P_closed(A, B), 6), round(P_angles(A, B, 1201), 6))
    best = (1, None)
    for A in np.linspace(0.5, 60, 240):
        for B in np.linspace(A, (180 - A) / 2, 120):
            p = P_closed(A, B)
            if p < best[0]: best = (p, (round(A, 3), round(B, 3)))
    print("grid minimum:", round(best[0], 7), "at angles", best[1], " 13/48 =", round(13 / 48, 7))
