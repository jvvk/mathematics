"""Test of the scaling conjecture for the first Fibonacci step (STATUS.md, transition analysis).

Conjecture: starting from a (1,2) front with up-angle irregularity eps and diameter law d = b0 + c*y,
the first Fibonacci step (1,2) -> (2,2) -> (3,2) without a pentagon happens iff |eps/c| < K, i.e. the
outcome depends on (eps, c) through eps/c in the limit c -> 0.

Full Schwendener stacking: each new disk goes to the lowest position tangent to two front disks and
overlapping none; the front disks strictly between its parents leave the front
(0 between: triangle, 1: rhombus, 2: pentagon).
"""
from __future__ import annotations
import math, os, sys
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from tracking_irregularity import lattice_front

Disk = tuple[float, float, float]  # x, y, d

def tangent_up(A: Disk, C: Disk, b0: float, c: float) -> Disk | None:
    ax, ay, ad = A; cx, cy, cd = C
    dq = min(ad, cd)
    for _ in range(60):
        r1, r2 = (ad + dq) / 2, (cd + dq) / 2
        dx, dy = cx - ax, cy - ay
        L = math.hypot(dx, dy)
        if L > r1 + r2 or L < abs(r1 - r2):
            return None
        a = (r1 * r1 - r2 * r2 + L * L) / (2 * L)
        h = math.sqrt(max(r1 * r1 - a * a, 0.0))
        qx, qy = ax + a * dx / L - h * dy / L, ay + a * dy / L + h * dx / L
        new = b0 + c * qy
        if abs(new - dq) < 1e-14:
            break
        dq = new
    return (qx, qy, dq)

def parastichy(F: list[Disk]) -> tuple[int, int]:
    N = len(F)
    ys = [F[k][1] for k in range(N)] + [F[0][1]]
    downs = sum(1 for k in range(N) if ys[k + 1] < ys[k])
    return downs, N - downs

def step(F: list[Disk], b0: float, c: float) -> tuple[list[Disk], int]:
    N = len(F)
    best = None
    for i in range(N):
        for g in range(0, min(3, N - 1)):  # g = number of disks strictly between parents
            j = (i + g + 1) % N
            A = F[i]
            C = F[j] if j > i else (F[j][0] + 1.0, F[j][1], F[j][2])
            if C[0] <= A[0]:
                continue
            Q = tangent_up(A, C, b0, c)
            if Q is None:
                continue
            ok = True
            for k in range(N):
                if k in (i, j):
                    continue
                for s in (-1.0, 0.0, 1.0):
                    if math.hypot(F[k][0] + s - Q[0], F[k][1] - Q[1]) < (F[k][2] + Q[2]) / 2 - 1e-11:
                        ok = False; break
                if not ok:
                    break
            if ok and (best is None or Q[1] < best[0][1]):
                best = (Q, i, g)
    Q, i, g = best
    removed = {(i + t + 1) % N for t in range(g)}
    G = [F[k] for k in range(N) if k not in removed] + [(Q[0] % 1.0, Q[1], Q[2])]
    G.sort(key=lambda p: p[0])
    return G, g

def outcome(beta: float, eps: float, c: float) -> str:
    F3, b = lattice_front(beta, eps)
    F: list[Disk] = [(p[0] % 1.0, p[1], p[2]) for p in F3]
    F.sort(key=lambda p: p[0])
    b0 = b
    path = [parastichy(F)]
    quiet = 0
    for n in range(int(40 / abs(c))):
        F, g = step(F, b0, c)
        p = parastichy(F)
        if g == 2:
            return "pentagon:" + "->".join(f"{a}{u}" for a, u in path + [p])
        if p != path[-1]:
            path.append(p); quiet = 0
        else:
            quiet += 1
        if len(path) >= 3:
            s = "->".join(f"{a}{u}" for a, u in path)
            return ("FIB " if path[1:3] == [(2, 2), (3, 2)] else "OTHER ") + s
    return "none:" + "->".join(f"{a}{u}" for a, u in path)

if __name__ == "__main__":
    beta = 0.45
    ratios = [-4, -3, -2, -1.5, -1, -0.5, 0, 0.5, 1, 1.5, 2, 3, 4]
    print(f"beta={beta}; rows c, columns eps/|c|; F = (1,2)->(2,2)->(3,2) with no pentagon")
    print("      c      " + " ".join(f"{r:>5}" for r in ratios))
    for c in (-0.004, -0.002, -0.001, -0.0005):
        row = []
        for r in ratios:
            o = outcome(beta, r * abs(c), c)
            row.append("F" if o.startswith("FIB") else ("P" if o.startswith("pent") else ("?" if o.startswith("none") else "O")))
        print(f"  {c:+.4f}   " + " ".join(f"{x:>5}" for x in row))
