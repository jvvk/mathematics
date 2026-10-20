"""Where does the Fibonacci route first break? (STATUS.md, transition analysis session 2)

From a (1,2) lattice front, full Schwendener stacking with d = b0 + c*y. The Fibonacci route
(golden-ratio scenario): from a Fibonacci pair base (p,q), triangles may only increase the SMALLER
coordinate, one at a time, until it reaches p+q; that state is the new base. A pentagon, a triangle
on the other coordinate, or a parent gap of 3+ disks is a BREAK. Report the step, the base pair
reached, and the event.
"""
from __future__ import annotations
import math, os, sys
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from tracking_irregularity import lattice_front
from transition_scaling import tangent_up, parastichy

Disk = tuple[float, float, float]

def step(F: list[Disk], b0: float, c: float) -> tuple[list[Disk], int]:
    N = len(F)
    best = None
    for i in range(N):
        for g in range(0, min(4, N - 1)):
            j = (i + g + 1) % N
            A = F[i]
            C = F[j] if j > i else (F[j][0] + 1.0, F[j][1], F[j][2])
            if C[0] <= A[0]:
                continue
            Q = tangent_up(A, C, b0, c)
            if Q is None or (best is not None and Q[1] >= best[0][1]):
                continue
            ok = True
            for k in range(N):
                if k == i or k == j:
                    continue
                for s in (-1.0, 0.0, 1.0):
                    if math.hypot(F[k][0] + s - Q[0], F[k][1] - Q[1]) < (F[k][2] + Q[2]) / 2 - 1e-11:
                        ok = False; break
                if not ok:
                    break
            if ok:
                best = (Q, i, g)
    Q, i, g = best
    removed = {(i + t + 1) % N for t in range(g)}
    G = [F[k] for k in range(N) if k not in removed] + [(Q[0] % 1.0, Q[1], Q[2])]
    G.sort(key=lambda p: p[0])
    return G, g

def run(beta: float, c: float, eps: float = 0.0, max_pair: int = 34, d_min: float = 0.015):
    F3, b = lattice_front(beta, eps)
    F = sorted([(p[0] % 1.0, p[1], p[2]) for p in F3])
    b0 = b
    base = parastichy(F)  # (1,2)
    cur = base
    n = 0
    while True:
        n += 1
        F, g = step(F, b0, c)
        if min(p[2] for p in F) < d_min:
            return n, base, "ran out (disks too small)"
        p = parastichy(F)
        if g >= 2:
            return n, base, f"{'pentagon' if g == 2 else 'gap3'} at {cur}->{p}"
        if p == cur:
            continue
        # triangle: exactly one coordinate +1
        small = 0 if base[0] < base[1] else 1
        grew = 0 if p[0] == cur[0] + 1 else (1 if p[1] == cur[1] + 1 else -1)
        if grew != small:
            return n, base, f"wrong-side triangle at {cur}->{p}"
        cur = p
        if cur[small] == base[0] + base[1]:
            base = cur
            if max(base) >= max_pair:
                return n, base, "reached target"

if __name__ == "__main__":
    import time
    for beta in (0.45,):
        print(f"beta={beta}, lattice start (1,2); route = Fibonacci bases reached before the first break")
        for c in (-0.3, -0.2, -0.15, -0.1, -0.07, -0.05, -0.035, -0.025):
            t0 = time.time()
            n, base, why = run(beta, c)
            print(f"  c={c:+.3f}  steps={n:6d}  last Fibonacci base={base}  {why}  ({time.time()-t0:.0f}s)", flush=True)
