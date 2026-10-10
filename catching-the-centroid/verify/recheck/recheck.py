"""Independent recheck of every number stated in note.tex. Shares no code with verify/*.py.

Own convex hull (monotone chain), own centroid (triangle fan), own clipping, own ray casting, polar quadrature by
scipy.integrate.quad with explicit breakpoints, and Monte Carlo by rejection sampling. Checks:
  T1  P(equilateral triangle) = 1/3 + ln3/6, P(square) = 1/2
  T2  Table 1: P, g, s for every row (to the printed six decimals; half-disc as a 3000-gon)
  T3  Figure 2 caption: P - 1/2 = 0.0164 (triangle) and 0.0024 (pentagon)
  T4  arithmetic of Theorem 1 and Section 4: 1/18 * 1/3 = 1/54, 1/2 + 1/54 = 14/27, 1/18 * 3/5 = 1/30, 1/2 + 1/30 = 8/15
  T5  Section 5 remark: 2550 of 3000 random polygons are three-sided (same random recipe, own counting)
  T6  Stewart's inequality, the input of Theorem 1: s >= 2/3 on 500 random convex polygons, including
      ones whose boundary crosses its reflection ten or more times
  T7  Monte Carlo agreement for P and s on the table's polygons
  M   three mutants of this file's own geometry must each break a check
Usage: python3 recheck.py [--quick]   (--quick skips the 3000-gon half-disc and lowers Monte Carlo sizes)
"""

from __future__ import annotations

import math
import sys
from pathlib import Path

import numpy as np
from scipy.integrate import quad

HERE = Path(__file__).resolve().parent
QUICK = "--quick" in sys.argv
FLAGS = {"near_side": False, "r_power": 2, "reflect_self": False}


# ---------- geometry (independent implementations) ----------
def hull(pts: np.ndarray) -> np.ndarray:
    """Andrew's monotone chain, counter-clockwise, no collinear points."""
    P = sorted(map(tuple, pts))

    def cross(o, a, b):
        return (a[0] - o[0]) * (b[1] - o[1]) - (a[1] - o[1]) * (b[0] - o[0])

    lower, upper = [], []
    for p in P:
        while len(lower) >= 2 and cross(lower[-2], lower[-1], p) <= 0:
            lower.pop()
        lower.append(p)
    for p in reversed(P):
        while len(upper) >= 2 and cross(upper[-2], upper[-1], p) <= 0:
            upper.pop()
        upper.append(p)
    return np.array(lower[:-1] + upper[:-1], dtype=float)


def area_centroid(V: np.ndarray) -> tuple[float, np.ndarray]:
    """Fan of triangles from vertex 0."""
    A, M = 0.0, np.zeros(2)
    for i in range(1, len(V) - 1):
        a = 0.5 * (
            (V[i][0] - V[0][0]) * (V[i + 1][1] - V[0][1])
            - (V[i][1] - V[0][1]) * (V[i + 1][0] - V[0][0])
        )
        A += a
        M += a * (V[0] + V[i] + V[i + 1]) / 3
    return A, M / A


def area(V: np.ndarray) -> float:
    return area_centroid(V)[0] if len(V) >= 3 else 0.0


def cut(V: np.ndarray, n: np.ndarray, c: float) -> np.ndarray:
    """Part of the convex polygon V with n.x <= c."""
    out = []
    for i in range(len(V)):
        p, q = V[i], V[(i + 1) % len(V)]
        fp, fq = n @ p - c, n @ q - c
        if fp <= 0:
            out.append(p)
        if (fp < 0 < fq) or (fq < 0 < fp):
            out.append(p + (q - p) * (fp / (fp - fq)))
    return np.array(out)


def ray(V: np.ndarray, G: np.ndarray, t: float) -> float:
    """Distance from G to the boundary in direction t."""
    u = np.array([math.cos(t), math.sin(t)])
    best = math.inf
    for i in range(len(V)):
        p, q = V[i] - G, V[(i + 1) % len(V)] - G
        e = q - p
        den = u[0] * e[1] - u[1] * e[0]
        if abs(den) < 1e-300:
            continue
        lam = (p[0] * e[1] - p[1] * e[0]) / den  # G + lam u on the edge line
        mu = (p[0] * u[1] - p[1] * u[0]) / den  # position along the edge
        if lam > 0 and -1e-12 <= mu <= 1 + 1e-12:
            best = min(best, lam)
    return best


def a_frac(V: np.ndarray, G: np.ndarray, A: float, t: float) -> float:
    """Share of the area in the half-plane through G facing away from direction t."""
    u = np.array([math.cos(t), math.sin(t)])
    if FLAGS["near_side"]:
        u = -u
    return area(cut(V, u, u @ G)) / A


def P_polar(V: np.ndarray) -> float:
    A, G = area_centroid(V)
    va = [math.atan2(*(v - G)[::-1]) % (2 * math.pi) for v in V]
    br = sorted(
        {x % (2 * math.pi) for a in va for x in (a, a + math.pi / 2, a - math.pi / 2)}
        | {0.0}
    )
    br.append(2 * math.pi)
    f = lambda t: ray(V, G, t) ** FLAGS["r_power"] / (2 * A) * a_frac(V, G, A, t)
    return sum(
        quad(f, lo, hi, epsabs=1e-13, epsrel=1e-12, limit=200)[0]
        for lo, hi in zip(br[:-1], br[1:])
        if hi > lo
    )


def radial_grid(
    V: np.ndarray, G: np.ndarray, t: np.ndarray, chunk: int = 2048
) -> np.ndarray:
    """r(t) from G for many angles: vectorised ray casting, in chunks of angles to keep memory small."""
    Pp, Q = V - G, np.roll(V, -1, axis=0) - G
    E = Q - Pp
    out = np.empty(len(t))
    for s0 in range(0, len(t), chunk):
        tt = t[s0 : s0 + chunk]
        ux, uy = np.cos(tt)[:, None], np.sin(tt)[:, None]
        den = ux * E[None, :, 1] - uy * E[None, :, 0]
        with np.errstate(divide="ignore", invalid="ignore"):
            lam = (
                Pp[None, :, 0] * E[None, :, 1] - Pp[None, :, 1] * E[None, :, 0]
            ) / den
            mu = (Pp[None, :, 0] * uy - Pp[None, :, 1] * ux) / den
        ok = (lam > 0) & (mu >= -1e-12) & (mu <= 1 + 1e-12)
        out[s0 : s0 + chunk] = np.where(ok, lam, np.inf).min(1)
    return out


def P_grid(V: np.ndarray, M: int = 1 << 17) -> float:
    """Second method, for polygons with many vertices: rho from r on a fine grid (midpoint rule), and a(t) from
    cumulative sums of rho over the half-turn [t + pi/2, t + 3pi/2]."""
    A, G = area_centroid(V)
    t = (np.arange(M) + 0.5) * 2 * np.pi / M
    r = radial_grid(V, G, t)
    rho = r ** FLAGS["r_power"] / (2 * A) * (2 * np.pi / M)
    if FLAGS["r_power"] == 2:
        rho = rho / rho.sum()
    c = np.concatenate([[0.0], np.cumsum(np.concatenate([rho, rho]))])
    k = np.arange(M)
    a = c[k + 3 * M // 4] - c[k + M // 4]
    if FLAGS["near_side"]:
        a = 1 - a
    return float(rho @ a)


def crossing_pairs(V: np.ndarray, M: int = 4096) -> int:
    A, G = area_centroid(V)
    t = (np.arange(M) + 0.5) * 2 * np.pi / M
    r = radial_grid(V, G, t)
    d = r - np.roll(r, M // 2)
    sg = np.sign(d[np.abs(d) > 1e-9 * r.max()])
    return int(np.sum(sg != np.roll(sg, 1))) // 2


def s_exact(V: np.ndarray) -> float:
    A, G = area_centroid(V)
    R = V if FLAGS["reflect_self"] else (2 * G - V)
    I = V.copy()
    for i in range(
        len(R)
    ):  # clip by each edge of R (counter-clockwise: inside is to the left)
        p, q = R[i], R[(i + 1) % len(R)]
        n = np.array([q[1] - p[1], p[0] - q[0]])
        I = cut(I, n, n @ p)
        if len(I) < 3:
            return 0.0
    return area(I) / A


def g_of(V: np.ndarray, m: int = 7200) -> float:
    A, G = area_centroid(V)
    best = max(
        abs(a_frac(V, G, A, t) - 0.5)
        for t in np.linspace(0, math.pi, m, endpoint=False)
    )
    return best


def inside(V: np.ndarray, X: np.ndarray) -> np.ndarray:
    ok = np.ones(len(X), bool)
    for i in range(len(V)):
        p, q = V[i], V[(i + 1) % len(V)]
        ok &= (q[0] - p[0]) * (X[:, 1] - p[1]) - (q[1] - p[1]) * (X[:, 0] - p[0]) >= 0
    return ok


def sample(V: np.ndarray, n: int, rng: np.random.Generator) -> np.ndarray:
    lo, hi = V.min(0), V.max(0)
    out = []
    while sum(len(o) for o in out) < n:
        X = lo + (hi - lo) * rng.random((2 * n, 2))
        out.append(X[inside(V, X)])
    return np.concatenate(out)[:n]


def mc(V: np.ndarray, n: int, rng: np.random.Generator) -> tuple[float, float]:
    A, G = area_centroid(V)
    X, Y = sample(V, n, rng) - G, sample(V, n, rng) - G
    return float(np.mean((X * Y).sum(1) <= 0)), float(np.mean(inside(V, G - X)))


# ---------- the checks ----------
def regular(n: int, rot: float = 0.0) -> np.ndarray:
    t = rot + 2 * np.pi * np.arange(n) / n
    return np.stack([np.cos(t), np.sin(t)], 1)


TRI = 1 / 3 + math.log(3) / 6
TABLE = [  # (name, polygon, P, g, s) as printed in Table 1
    ("square", np.array([[0, 0], [1, 0], [1, 1], [0, 1.0]]), 0.500000, 0.0, 1.0),
    ("regular pentagon", regular(5), 0.499054, 0.010557, 0.894427),
    ("half-disc", None, 0.501321, 0.034468, 0.814753),
    ("triangle 3,4,5", np.array([[0, 0], [4, 0], [0, 3.0]]), 0.506629, 1 / 18, 2 / 3),
    ("right isosceles", np.array([[0, 0], [1, 0], [0, 1.0]]), 0.509825, 1 / 18, 2 / 3),
    (
        "triangle (0,0),(1,0),(0.2,0.7)",
        np.array([[0, 0], [1, 0], [0.2, 0.7]]),
        0.510138,
        1 / 18,
        2 / 3,
    ),
    ("equilateral triangle", regular(3), 0.516435, 1 / 18, 2 / 3),
]


def checks() -> list[str]:
    fails: list[str] = []

    def need(cond: bool, msg: str) -> None:
        print(("ok    " if cond else "FAIL  ") + msg)
        if not cond:
            fails.append(msg)

    rng = np.random.default_rng(2026)
    # T1
    p3, p4 = P_polar(regular(3)), P_polar(TABLE[0][1])
    need(
        abs(p3 - TRI) < 1e-9,
        f"T1 P(equilateral) = {p3:.12f} vs 1/3 + ln3/6 = {TRI:.12f}",
    )
    need(abs(p4 - 0.5) < 1e-9, f"T1 P(square) = {p4:.12f}")
    # T2
    for name, V, P0, g0, s0 in TABLE:
        if V is None:
            if QUICK:
                continue
            th = np.linspace(0, np.pi, 3001)
            V = hull(np.stack([np.cos(th), np.sin(th)], 1))
        V = hull(V)
        p = P_grid(V) if name == "half-disc" else P_polar(V)
        s = s_exact(V)
        g = g_of(V, 1800 if name == "half-disc" else 7200)
        need(
            abs(p - P0) < 6e-7 and abs(s - s0) < 6e-7 and abs(g - g0) < 2e-6,
            f"T2 {name}: P {p:.6f} (table {P0:.6f}), g {g:.6f} ({g0:.6f}), s {s:.6f} ({s0:.6f})",
        )
    # T3
    pent = hull(np.array([[0, 0], [3, 0], [3.5, 1], [1, 2.2], [-0.4, 1.0]]))
    d3, d5 = P_polar(regular(3)) - 0.5, P_polar(pent) - 0.5
    need(
        round(d3, 4) == 0.0164 and round(d5, 4) == 0.0024,
        f"T3 Figure 2: {d3:.6f}, {d5:.6f}",
    )
    # T4
    need(
        abs(1 / 18 * 3 / 5 - 1 / 30) < 1e-15
        and abs(0.5 + 1 / 30 - 8 / 15) < 1e-15
        and abs(1 / 18 / 3 - 1 / 54) < 1e-15
        and abs(0.5 + 1 / 54 - 14 / 27) < 1e-15,
        "T4 arithmetic",
    )
    # T5: same random recipe as verify/searches.py, independent hull and crossing count
    r2 = np.random.default_rng(31)
    cnt: dict[int, int] = {}
    for _ in range(3000 if not QUICK else 300):
        n = int(r2.integers(5, 11))
        ang = np.sort(r2.random(n) * 2 * np.pi)
        P = np.stack([np.cos(ang), np.sin(ang)], 1) * r2.uniform(
            0.7, 1.3, size=(n, 1)
        ) + r2.normal(scale=0.15, size=2)
        V = hull(P)
        m = crossing_pairs(V)
        cnt[m] = cnt.get(m, 0) + 1
    if not QUICK:
        need(
            cnt.get(3) == 2550 and sum(cnt.values()) == 3000,
            f"T5 three-sided count {dict(sorted(cnt.items()))}",
        )
    # T6
    r3 = np.random.default_rng(77)
    low, many = 2.0, 0
    for _ in range(500 if not QUICK else 60):
        n = int(r3.integers(3, 12))
        V = hull(r3.normal(size=(n, 2)) * r3.uniform(0.3, 1.5, size=2))
        low = min(low, s_exact(V))
        many += crossing_pairs(V) >= 5
    need(low >= 2 / 3 - 1e-9 and (many > 0 or QUICK), f"T6 Stewart: min s = {low:.9f}, {many} polygons with >= 10 crossings")
    # T7
    N = 400_000 if QUICK else 2_000_000
    for name, V, P0, g0, s0 in TABLE:
        if V is None:
            continue
        V = hull(V)
        p, s = mc(V, N, rng)
        tol = 5 * math.sqrt(0.25 / N)
        need(
            abs(p - P0) < tol and abs(s - s0) < tol,
            f"T7 Monte Carlo {name}: P {p:.5f}, s {s:.5f}",
        )
    return fails


if __name__ == "__main__":
    sys.stdout.reconfigure(line_buffering=True)
    fails = checks()
    print(f"\n{'ALL CHECKS PASS' if not fails else f'{len(fails)} FAILED'}")
    # mutants of this file's own geometry: each must break at least one check
    QUICK = True
    killed = 0
    for key, val in (("near_side", True), ("r_power", 1), ("reflect_self", True)):
        old = FLAGS[key]
        FLAGS[key] = val
        print(f"\n--- mutant {key} = {val}")
        killed += bool(checks())
        FLAGS[key] = old
    print(f"\nmutants killed: {killed}/3")
    sys.exit(0 if not fails and killed == 3 else 1)
