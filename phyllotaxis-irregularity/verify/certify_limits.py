"""Certified (interval-arithmetic) candidate analysis at the limiting tilings of the ratio-law proof.

Unit diameters (c = 0 limit). A front is a cyclic list of unit vectors (left to right) with period L = sum of
x-components. Candidate = disk tangent to two front disks P = z_a, R = z_b (b = a + gap + 1, cyclic), above the
segment, not overlapping any front disk (tangency allowed). All comparisons in mpmath interval arithmetic:
a comparison whose interval straddles the threshold is reported as TIE (an exact degeneracy to be treated by
the first-order lemmas), never silently decided.
"""
from __future__ import annotations
from mpmath import iv, mp
iv.dps = 40

S3, S7, S19 = iv.sqrt(3), iv.sqrt(7), iv.sqrt(19)

def vec(cx, sx):
    return (cx, sx)

def add(p, q): return (p[0] + q[0], p[1] + q[1])
def sub(p, q): return (p[0] - q[0], p[1] - q[1])
def d2(p, q): return (p[0] - q[0]) ** 2 + (p[1] - q[1]) ** 2

def lt(a, b):  # certified a < b ; None if undecided
    if a.b < b.a: return True
    if a.a > b.b: return False
    return None

def apex(P, R):
    dx, dy = R[0] - P[0], R[1] - P[1]
    L2 = dx * dx + dy * dy
    if lt(L2, iv.mpf(4)) is not True:
        return None
    k = iv.sqrt(1 / L2 - iv.mpf(1) / 4)  # height factor: apex = M + k * (-dy, dx)
    M = ((P[0] + R[0]) / 2, (P[1] + R[1]) / 2)
    return (M[0] - k * dy, M[1] + k * dx)

def front_points(vectors):
    pts = [(iv.mpf(0), iv.mpf(0))]
    for v in vectors[:-1]:
        pts.append(add(pts[-1], v))
    end = add(pts[-1], vectors[-1])
    L = end[0]
    assert lt(abs(end[1]), iv.mpf(10) ** -30), "front does not close vertically"
    return pts, L

def candidates(vectors, names):
    pts, L = front_points(vectors)
    N = len(pts)
    out = []
    for a in range(N):
        for gap in range(0, N - 1):
            b = a + gap + 1
            R = pts[b % N] if b < N else (pts[b % N][0] + L, pts[b % N][1])
            Q = apex(pts[a], R)
            if Q is None:
                continue
            status = "valid"
            for k in range(N):
                if k in (a, b % N):
                    continue
                for sh in (-1, 0, 1):
                    Pk = (pts[k][0] + sh * L, pts[k][1])
                    r = lt(d2(Q, Pk), iv.mpf(1))
                    if r is True:
                        status = "overlap"; break
                    if r is None:
                        status = "TIE(tangent to %s)" % names[k] if status == "valid" else status
                if status == "overlap":
                    break
            if status != "overlap":
                out.append((Q[1], gap, a, b % N, status, Q[0]))
    out.sort(key=lambda t: t[0].a)
    return out, L

def show(title, vectors, names):
    cs, L = candidates(vectors, names)
    print(f"== {title}  (period L = {mp.nstr(L.mid, 12)})")
    y0 = cs[0][0]
    for y, gap, a, b, st, x in cs[:8]:
        dy = y - y0
        print(f"   {'TRPH'[min(gap,3)]} on ({names[a]},{names[b]}) gap {gap}: height-above-lowest in "
              f"[{mp.nstr(dy.a, 8)}, {mp.nstr(dy.b, 8)}]  x={mp.nstr(x.mid, 6)}  {st}")
    return cs

# ---------- (A) K0: (3,2) threshold lattice after two burst triangles: word U S U S U U D ----------
U = vec(7 / (2 * S19), 3 * S3 / (2 * S19))      # beta_U = beta_D + 60, tan beta_D = -sqrt3/4
Sv = vec(1 / (2 * S19), -5 * S3 / (2 * S19))    # steep child beta_D - 60
D = vec(4 / S19, -S3 / S19)
# names = disk at the START of each vector; z1 = apex of the burst triangle on D (lineage D/+ then D/-)
show("K0 at placement (word D/+ D/- Ua/-/+ Ua/-/- Ub/+ Ua/+ Ub/-)", [U, Sv, U, Sv, U, U, D],
     ["z0", "z1(burst)", "z2", "z3=P0", "z4=P1", "z5=P2", "z6=P3"])

# ---------- (B) step-1 (2,2) phase at the (1,2) threshold lattice, eps -> 0 ----------
U1 = vec(5 / (2 * S7), S3 / (2 * S7))            # beta_U = 19.107 deg, tan beta_D = -sqrt3/2
U60 = vec(-1 / (2 * S7) + 0 * S7, None) if False else None
# U rotated +60: cos = cos/2 - sin*sqrt3/2, sin = sin/2 + cos*sqrt3/2
U1p = (U1[0] / 2 - U1[1] * S3 / 2, U1[1] / 2 + U1[0] * S3 / 2)
D1 = vec(2 / S7, -S3 / S7)
for title, vs, nm in (
    ("(2,2) word 1: Ua D Ub/+ Ub/-", [U1, D1, U1p, D1], ["Ua", "D", "Ub/+", "Ub/-"]),
    ("(2,2) word 2: Ua Ub/- D Ub/+", [U1, D1, D1, U1p], ["Ua", "Ub/-", "D", "Ub/+"]),
    ("(2,2) word 3: Ua Ub/- Ub/+ D", [U1, D1, U1p, D1], ["Ua", "Ub/-", "Ub/+", "D"]),
    ("(2,2) word 4: Ua D Ub/- Ub/+", [U1, D1, D1, U1p], ["Ua", "D", "Ub/-", "Ub/+"]),
):
    show(title, vs, nm)
