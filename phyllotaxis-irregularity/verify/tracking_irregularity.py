"""Test of the first-order claim in STATUS.md ("tracking phase").

Model: Schwendener disk stacking on a cylinder of circumference 1 (unrolled, x mod 1).
Disk diameter depends on its height: d(y) = b0 + c*y (c < 0: disks shrink upward), as in
Golé-Dumais-Douady 2016. Tangent disks i, j have centre distance (d_i + d_j)/2.
Front: 3 disks (parastichy numbers (1,2): one down vector, two up vectors).
Each step: the unique notch (down vector followed by up vector) receives a new disk tangent
to the notch's two walls; the notch bottom leaves the front. We stop at the first step whose
notch hinge angle reaches 2*pi/3 (a triangle transition is then possible).

Claim tested: irregularity eps = beta_a - beta_b (difference of the two up-vector angles)
(i)  starting on a lattice (eps0 = 0) stays O(|c|) up to the transition;
(ii) starting at eps0 small, eps_final/eps0 tends to a limit K independent of c as c -> 0
     (slow linear evolution d eps/d(slow time) = M eps; the lattice family is invariant
     to first order, so there is no O(c)-per-step source term).
"""
from __future__ import annotations
import math

def place(A: tuple[float, float, float], C: tuple[float, float, float], b0: float, c: float) -> tuple[float, float, float]:
    """New disk (x, y, d) tangent to A and C, on the upper side; d = b0 + c*y solved by fixed point."""
    ax, ay, ad = A
    cx, cy, cd = C
    dq = ad
    for _ in range(60):
        r1, r2 = (ad + dq) / 2, (cd + dq) / 2
        dx, dy = cx - ax, cy - ay
        L = math.hypot(dx, dy)
        a = (r1 * r1 - r2 * r2 + L * L) / (2 * L)
        h = math.sqrt(max(r1 * r1 - a * a, 0.0))
        ux, uy = dx / L, dy / L
        qx, qy = ax + a * ux - h * uy, ay + a * uy + h * ux  # left normal of A->C points up
        new = b0 + c * qy
        if abs(new - dq) < 1e-15:
            break
        dq = new
    return (qx, qy, dq)

def lattice_front(beta: float, eps: float) -> tuple[list[tuple[float, float, float]], float]:
    """3-chain with up angles beta+eps/2, beta-eps/2, closing around circumference 1 at height 0."""
    ba, bb = beta + eps / 2, beta - eps / 2
    # unknown b and down angle bd: b(cos ba + cos bb + cos bd) = 1, sin ba + sin bb + sin bd = 0
    bd = -math.asin(math.sin(ba) + math.sin(bb))
    b = 1.0 / (math.cos(ba) + math.cos(bb) + math.cos(bd))
    A = (0.0, 0.0, b)
    B = (A[0] + b * math.cos(bd), A[1] + b * math.sin(bd), b)
    C = (B[0] + b * math.cos(ba), B[1] + b * math.sin(ba), b)
    return [A, B, C], b

def angle(P, Q) -> float:
    return math.atan2(Q[1] - P[1], Q[0] - P[0])

def run(beta: float, eps0: float, c: float, max_steps: int = 10**7) -> tuple[int, float, float]:
    F, b = lattice_front(beta, eps0)
    b0 = b  # all initial disks at height ~0 share diameter b; y-shift below
    # shift so that b0 + c*y matches: initial disks keep diameter b (bottom row is given data)
    for n in range(max_steps):
        pts = F + [(F[0][0] + 1.0, F[0][1], F[0][2])]
        vecs = [(pts[i + 1][0] - pts[i][0], pts[i + 1][1] - pts[i][1]) for i in range(3)]
        k = next(i for i in range(3) if vecs[i][1] < 0 and vecs[(i + 1) % 3][1] > 0)
        Ai, Bi, Ci = k, (k + 1) % 3, (k + 2) % 3
        A, Bp, C = F[Ai], F[Bi], F[Ci]
        if Ci < Ai or (Ci == 0):  # wrap: C lies one period to the right of A
            pass
        A_ = A
        C_ = C if C[0] > A[0] else (C[0] + 1.0, C[1], C[2])
        B_ = Bp if Bp[0] > A[0] else (Bp[0] + 1.0, Bp[1], Bp[2])
        # hinge angle at notch bottom B between B->A and B->C
        t = abs(angle(B_, A_) - angle(B_, C_))
        t = min(t, 2 * math.pi - t)
        ups = [i for i in range(3) if vecs[i][1] > 0]
        ua = math.atan2(vecs[ups[0]][1], vecs[ups[0]][0])
        ub = math.atan2(vecs[ups[1]][1], vecs[ups[1]][0])
        if t >= 2 * math.pi / 3:
            return n, ua - ub, t
        Q = place(A_, C_, b0, c)
        Q = (Q[0] % 1.0, Q[1], Q[2])
        F = [F[i] if i != Bi else Q for i in range(3)]
        F.sort(key=lambda p: p[0])
    return max_steps, float("nan"), float("nan")

if __name__ == "__main__":
    beta = 0.45  # valid 3-chain needs 2 sin(beta) < 1, i.e. beta < 0.5236
    print("beta =", beta)
    print("(i) lattice start, eps0 = 0")
    for c in (-0.08, -0.04, -0.02, -0.01, -0.005):
        n, e, t = run(beta, 0.0, c)
        print(f"  c={c:+.3f} steps={n:6d} eps_final={e:.3e} eps/|c|={e/abs(c):.4f}")
    print("(ii) linear response K = (eps(eps0) - eps(0)) / eps0, eps0 = +-1e-4")
    for c in (-0.02, -0.01, -0.005, -0.0025, -0.00125, -0.000625):
        for e0 in (1e-4, -1e-4):
            n, e, t = run(beta, e0, c)
            n0, z, _ = run(beta, 0.0, c)
            print(f"  c={c:+.6f} eps0={e0:+.0e} steps={n:6d} (lattice {n0:6d}) K={abs(e - z) / abs(e0) if n == n0 else float('nan'):.5f} raw={e:+.3e} lat={z:+.3e}")
