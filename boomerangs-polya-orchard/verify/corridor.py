"""Explicit corridor arcs: lower bound B(r) >= 2(1-r)cot(alpha/2) - (1-r) ~ 4/r.

The arc leaves O at angle alpha right of vertical, turning left, with
a(1 - cos alpha) = 1 - r, so it stays in r <= x <= 1 - r from height 1 - r until it comes
back to x = r. Needs x(1 - r) >= r; alpha is (just above) the least angle with that property.
"""
from __future__ import annotations

import math
import sys

from scipy.optimize import brentq


def x_at(y: float, alpha: float, r: float) -> float:
    a = (1 - r) / (1 - math.cos(alpha))
    return math.sqrt(a * a - (y - a * math.sin(alpha)) ** 2) - a * math.cos(alpha)


def corridor(r: float) -> tuple[float, float, float]:
    alpha = brentq(lambda t: x_at(1 - r, t, r) - r, r / 10, 1.0, xtol=1e-15) * (1 + 1e-9)
    a = (1 - r) / (1 - math.cos(alpha))
    reach = 2 * (1 - r) / math.tan(alpha / 2) - (1 - r)
    return reach, a, alpha


if __name__ == "__main__":
    for inv in map(float, sys.argv[1:]):
        reach, a, alpha = corridor(1 / inv)
        print(f"1/r={inv:6.0f}  corridor reach>={reach:10.3f}  reach*r={reach/inv:.4f}  "
              f"a={a!r} theta={math.pi / 2 - alpha!r}")
