"""Independent check of an arc: sample it densely, measure clearance to the nearest tree."""
from __future__ import annotations

import math
import sys

import numpy as np


def clearance_profile(a: float, theta: float, smax: float, n: int = 400_000):
    s = np.linspace(1e-9, smax, n)
    ang = theta + np.arcsin(np.minimum(s / (2 * a), 1.0))
    x, y = s * np.cos(ang), s * np.sin(ang)
    gx, gy = np.rint(x), np.rint(y)
    best = np.full(n, np.inf)
    for dx in (-1, 0, 1):
        for dy in (-1, 0, 1):
            qx, qy = gx + dx, gy + dy
            d = np.hypot(x - qx, y - qy)
            d[(qx == 0) & (qy == 0)] = np.inf
            best = np.minimum(best, d)
    return s, best


if __name__ == "__main__":
    a, theta, r, reach = map(float, sys.argv[1:5])
    s, c = clearance_profile(a, theta, min(2 * a, reach * 1.0))
    print(f"min clearance up to reach (should be >= r={r}): {c.min():.6f}")
    s2, c2 = clearance_profile(a, theta, min(2 * a, reach + 0.05), 50_000)
    bad = s2[c2 < r]
    print("first s with clearance < r:", bad[0] if len(bad) else None)
