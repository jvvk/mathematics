"""Values for Table 1 of the note: P, g = max half-plane imbalance, s = |K cap (2c-K)|/|K|, bound g(1-s)."""
from __future__ import annotations
import numpy as np
import exact
from core import area_centroid, regular

def g_of(V: np.ndarray, M: int = 20000) -> float:
    """max over lines through the centroid of |area on one side / |K| - 1/2|: grid, then ternary refinement."""
    A, c = area_centroid(V)
    W = V - c
    f = lambda ts: np.abs(exact.halfplane_areas(W, np.atleast_1d(ts)) / A - 0.5)  # noqa: E731
    t = np.linspace(0, np.pi, M, endpoint=False)
    vals = f(t)
    k = int(np.argmax(vals))
    lo, hi, best = t[k] - np.pi / M, t[k] + np.pi / M, float(vals[k])
    for _ in range(80):
        m1, m2 = lo + (hi - lo) / 3, hi - (hi - lo) / 3
        f1, f2 = float(f(m1)[0]), float(f(m2)[0])
        if f1 < f2:
            lo = m1
        else:
            hi = m2
        best = max(best, f1, f2)
    return best


th = np.linspace(0, np.pi, 3001)
SHAPES = {
    "square": np.array([[0, 0], [1, 0], [1, 1], [0, 1.0]]),
    "regular pentagon": regular(5),
    "half-disc (3000-gon)": np.vstack([np.stack([np.cos(th), np.sin(th)], 1)])[::-1][::-1],
    "right isosceles triangle": np.array([[0, 0], [1, 0], [0, 1.0]]),
    "triangle with sides 3, 4, 5": np.array([[0, 0], [4, 0], [0, 3.0]]),
    "triangle (0,0), (1,0), (0.2,0.7)": np.array([[0, 0], [1, 0], [0.2, 0.7]]),
    "equilateral triangle": regular(3),
}
if __name__ == "__main__":
    print(f"{'shape':34s} {'P':>10s} {'g':>10s} {'s':>10s} {'1/2+g(1-s)':>11s}")
    for k, V in SHAPES.items():
        p, g, s = exact.prob(V), g_of(V), exact.phi(V)
        print(f"{k:34s} {p:10.6f} {g:10.6f} {s:10.6f} {0.5 + g * (1 - s):11.6f}")
    print("1/3 + ln3/6 =", 1 / 3 + np.log(3) / 6, " 14/27 =", 14 / 27, " 8/15 =", 8 / 15)
