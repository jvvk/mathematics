"""Independent re-implementation of Schwendener disk stacking with d = b0 + c*y, written without
reusing multi_step.py / transition_scaling.py, to check the ratio-law pentagon.

Differences from the first simulator (deliberate):
- diameter of the new disk solved by bisection on its height (not fixed-point iteration);
- parents: ANY pair of front disks (any number of front disks between them);
- overlap test against ALL disks placed in the last `memory` steps plus the initial front, with
  periodic images (not only front disks);
- event type from the change in front length: +1 triangle, 0 rhombus, -1 pentagon, <= -2 other;
- front stored as a cyclic list of disk ids; parastichy numbers from the sign of height steps.
"""
from __future__ import annotations
import math

class Stack:
    def __init__(self, front_pts: list[tuple[float, float, float]], b0: float, c: float, tol: float = 1e-11, memory: int = 400):
        self.b0, self.c, self.tol, self.memory = b0, c, tol, memory
        self.disks: list[tuple[float, float, float]] = []  # (x mod 1, y, d)
        for x, y, d in front_pts:
            self.disks.append((x % 1.0, y, d))
        order = sorted(range(len(self.disks)), key=lambda k: self.disks[k][0])
        self.front: list[int] = order  # cyclic, increasing x

    def diam(self, y: float) -> float:
        return self.b0 + self.c * y

    def apex(self, P, R):
        """Disk tangent to P (left) and R (right, already unwrapped), above the segment P->R,
        with its own diameter d = diam(y). Solve g(y) = 0 by bisection on y."""
        px, py, pd = P; rx, ry, rd = R
        def pos(d):
            r1, r2 = (pd + d) / 2, (rd + d) / 2
            dx, dy = rx - px, ry - py
            L = math.hypot(dx, dy)
            if L > r1 + r2 or L < abs(r1 - r2):
                return None
            a = (r1 * r1 - r2 * r2 + L * L) / (2 * L)
            h = math.sqrt(max(r1 * r1 - a * a, 0.0))
            return (px + a * dx / L - h * dy / L, py + a * dy / L + h * dx / L)
        # g(d) = d - diam(y(d)); y(d) increasing in d; bracket d in [dmin, dmax]
        lo, hi = 1e-6, 4 * max(pd, rd)
        def g(d):
            q = pos(d)
            return None if q is None else d - self.diam(q[1])
        glo, ghi = g(lo), g(hi)
        if glo is None or ghi is None or glo * ghi > 0:
            # fall back: scan for a valid bracket
            ds = [lo + (hi - lo) * k / 200 for k in range(201)]
            vals = [(d, g(d)) for d in ds]
            vals = [(d, v) for d, v in vals if v is not None]
            br = [(vals[k][0], vals[k + 1][0]) for k in range(len(vals) - 1) if vals[k][1] * vals[k + 1][1] <= 0]
            if not br:
                return None
            lo, hi = br[0]
        for _ in range(80):
            mid = (lo + hi) / 2
            gm = g(mid)
            if gm is None:
                return None
            if (gm > 0) == (g(lo) > 0):
                lo = mid
            else:
                hi = mid
        d = (lo + hi) / 2
        q = pos(d)
        return None if q is None else (q[0], q[1], d)

    def free(self, Q, skip: set[int]) -> bool:
        n = len(self.disks)
        start = max(0, n - self.memory)
        cand = set(range(start, n)) | set(self.front)
        for k in cand:
            if k in skip:
                continue
            x, y, d = self.disks[k]
            for s in (-1.0, 0.0, 1.0):
                if math.hypot(x + s - Q[0], y - Q[1]) < (d + Q[2]) / 2 - self.tol:
                    return False
        return True

    def step(self) -> int:
        F = self.front
        N = len(F)
        best = None
        for a in range(N):
            for gap in range(0, N - 1):
                bidx = (a + gap + 1) % N
                P = self.disks[F[a]]
                R = self.disks[F[bidx]]
                if bidx <= a:
                    R = (R[0] + 1.0, R[1], R[2])
                if R[0] <= P[0]:
                    continue
                Q = self.apex(P, R)
                if Q is None or (best is not None and Q[1] >= best[0][1]):
                    continue
                if self.free(Q, {F[a], F[bidx]}):
                    best = (Q, a, gap)
        Q, a, gap = best
        self.disks.append((Q[0] % 1.0, Q[1], Q[2]))
        new_id = len(self.disks) - 1
        keep = [F[(a + k) % N] for k in range(N) if not (1 <= ((k - a - 1) % N) + 1 <= gap) or True]
        # rebuild front: remove the `gap` disks strictly after position a, insert new disk after a
        removed = {F[(a + t + 1) % N] for t in range(gap)}
        G = [i for i in F if i not in removed] + [new_id]
        G.sort(key=lambda i: self.disks[i][0])
        old_len = N
        self.front = G
        return len(G) - old_len  # +1 T, 0 R, -1 P

    def parastichy(self) -> tuple[int, int]:
        ys = [self.disks[i][1] for i in self.front]
        ys.append(ys[0])
        downs = sum(1 for k in range(len(self.front)) if ys[k + 1] < ys[k])
        return downs, len(self.front) - downs

def initial_front(beta: float, eps: float):
    """(1,2) chain with up angles beta +- eps/2, closing over circumference 1 (written afresh)."""
    ua, ub = beta + eps / 2, beta - eps / 2
    s = math.sin(ua) + math.sin(ub)
    bd = -math.asin(s)
    b = 1.0 / (math.cos(ua) + math.cos(ub) + math.cos(bd))
    A = (0.0, 0.0, b)
    B = (b * math.cos(bd), b * math.sin(bd), b)
    C = (B[0] + b * math.cos(ua), B[1] + b * math.sin(ua), b)
    return [A, B, C], b

def history(beta: float, eps: float, c: float, max_steps: int, tol: float = 1e-11, stop_at_pentagon: bool = True):
    pts, b = initial_front(beta, eps)
    S = Stack(pts, b, c, tol=tol)
    ev = []
    cur = S.parastichy()
    for n in range(1, max_steps + 1):
        dl = S.step()
        p = S.parastichy()
        if dl != 0 or p != cur:
            kind = {1: "T", 0: "R", -1: "P"}.get(dl, f"X{dl}")
            ev.append((n, kind, cur, p))
            cur = p
            if stop_at_pentagon and kind not in ("T", "R"):
                break
            if max(p) >= 8 and min(p) >= 5:
                break
    return ev

if __name__ == "__main__":
    cases = [(0.523, 0.005, -0.001), (0.523, 0.005, -0.002), (0.523, 0.01, -0.002), (0.523, 0.01, -0.005),
             (0.45, 0.01, -0.002), (0.45, 0.01, -0.005), (0.45, 0.0, -0.001)]
    for beta, eps, c in cases:
        ev = history(beta, eps, c, max_steps=int(30 / abs(c)))
        print(f"beta={beta} eps={eps} c={c} ratio={eps/abs(c):.1f}: " + "  ".join(f"{n}{k}{p}" for n, k, _, p in ev), flush=True)
