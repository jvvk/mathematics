"""Test of the (m,n) conjecture in STATUS.md (Lemma 1 generalisation).

Conjecture: in a rhombic phase of disk stacking with d = b0 + c*y, every up vector is multiplied by
prod over the downs it swaps with of (1 + i c e^{i beta_D}), and every down by prod over ups of
(1 - i c e^{i beta_U}), to first order. Over a phase of ~1/|c| steps each up swaps with each down
(almost) equally often, so all up/up and down/down complex ratios are invariant up to O(|c|).

Test: perturb a lattice front by eps (complex ratios r = V_k / V_1 differ from 1 by O(eps)); run the
exact stacking until a triangle becomes possible; compare final ratios with the unperturbed (lattice)
run. Prediction: (r_final - r_final_lattice) / (r_0 - 1) -> 1 as c -> 0, for every same-type pair.
"""
from __future__ import annotations
import cmath, math, os, sys
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from tracking_irregularity import place

Disk = tuple[complex, float]  # centre, diameter

def make_front(word: str, beta_u: float, ups_eps: list[float], down_split: float = 0.0) -> tuple[list[Disk], list[int]]:
    """Front from a word over {D,U}. Up k has angle beta_u + t + ups_eps[k]; the two downs have angles
    beta_d + t +- down_split, beta_d from the lattice; all lengths b. (t, b) solved by Newton so the
    chain closes around circumference 1 (t = 0 and the lattice b when all offsets vanish)."""
    m, n = word.count("D"), word.count("U")
    assert m == 2, "only m = 2 implemented"
    bd = -math.asin(n / m * math.sin(beta_u))
    offs_u = [beta_u + e for e in ups_eps]
    offs_d = sorted([bd + down_split, bd - down_split])
    def resid(t: float, b: float) -> complex:
        return b * sum(cmath.exp(1j * (a + t)) for a in offs_u + offs_d) - 1.0
    t, b = 0.0, 1.0 / (n * math.cos(beta_u) + m * math.cos(bd))
    for _ in range(50):
        r = resid(t, b)
        h = 1e-8
        jt = (resid(t + h, b) - r) / h
        jb = (resid(t, b + h) - r) / h
        det = jt.real * jb.imag - jt.imag * jb.real
        dt = (r.real * jb.imag - r.imag * jb.real) / det
        db = (jt.real * r.imag - jt.imag * r.real) / det
        t, b = t - dt, b - db
        if abs(r) < 1e-15:
            break
    ups = [b * cmath.exp(1j * (a + t)) for a in offs_u]
    downs = [b * cmath.exp(1j * (a + t)) for a in offs_d]
    vecs, labels, ku, kd = [], [], 0, 0
    for ch in word:
        if ch == "U":
            vecs.append(ups[ku]); labels.append(ku); ku += 1
        else:
            vecs.append(downs[kd]); labels.append(100 + kd); kd += 1
    pts, z = [], 0j
    for v in vecs:
        pts.append((z, b)); z += v
    assert abs(z - 1.0) < 1e-10, abs(z - 1.0)
    return pts, labels

def hinge(A: complex, B: complex, C: complex) -> float:
    t = abs(cmath.phase((A - B) / (C - B)))
    return t

def run(word: str, beta_u: float, ups_eps: list[float], c: float, max_steps: int = 10**6, split: float = 0.0):
    F, lab = make_front(word, beta_u, ups_eps, split)  # lab[k] = label of vector from F[k] to F[k+1]
    b0 = F[0][1]
    N = len(F)
    for step in range(max_steps):
        pts = [F[k][0] for k in range(N)] + [F[0][0] + 1.0]
        vec = [pts[k + 1] - pts[k] for k in range(N)]
        best = None
        for k in range(N):
            k1 = (k + 1) % N
            if vec[k].imag < 0 and vec[k1].imag > 0:  # notch: down then up, bottom at F[k1]
                A = F[k][0]
                B = A + vec[k]
                C = B + vec[k1]
                if hinge(A, B, C) >= 2 * math.pi / 3:
                    return step, F, lab, "triangle-possible"
                Q = place((A.real, A.imag, F[k][1]), (C.real, C.imag, F[(k + 2) % N][1]), b0, c)
                if best is None or Q[1] < best[0][1]:
                    best = (Q, k)
        Q, k = best
        k1 = (k + 1) % N
        Qz = complex(Q[0], Q[1])
        # overlap check against all front disks other than the two parents and the removed bottom
        for j in range(N):
            if j in (k, k1, (k + 2) % N):
                continue
            for shift in (-1.0, 0.0, 1.0):
                if abs(F[j][0] + shift - Qz) < (F[j][1] + Q[2]) / 2 - 1e-12:
                    return step, F, lab, "overlap"
        # replace bottom disk F[k1] by Q (keep x-coordinate continuity, no mod needed for ratios)
        if k1 == 0:
            Qz -= 1.0  # bottom was the wrapped first point
        F[k1] = (Qz, Q[2])
        lab[k], lab[k1] = lab[k1], lab[k]  # rhombic swap: D,U -> U,D
        # renormalise so the front starts at index 0 consistently (no re-sorting needed)
    return max_steps, F, lab, "max"

def vectors_by_label(F, lab) -> dict[int, complex]:
    N = len(F)
    pts = [F[k][0] for k in range(N)] + [F[0][0] + 1.0]
    return {lab[k]: pts[k + 1] - pts[k] for k in range(N)}

if __name__ == "__main__":
    eps = [0.0, 1.0, -0.6]
    # rhombic regime for (2,3) lattice needs beta_u + asin(1.5 sin beta_u) > pi/3 and 1.5 sin beta_u < 1
    for word, beta in (("DUDUU", 0.45), ("DUDUU", 0.55), ("DUUDU", 0.50)):
      print(f"front {word} (m,n)=(2,3), beta_u={beta}, ups perturbation shape {eps}, down split 0.7")
      for c in (-0.004, -0.002, -0.001, -0.0005, -0.00025):
        for scale in (1e-4,):
            e = [scale * x for x in eps]
            s1, F1, L1, why1 = run(word, beta, e, c, split=0.7 * scale)
            s0, F0, L0, why0 = run(word, beta, [0.0] * 3, c)
            assert s1 > 0 and s0 > 0, "zero-step run: start is outside the rhombic regime"
            n = min(s1, s0)  # compare at the same step: the stop step can differ by one
            s1, F1, L1, why1 = run(word, beta, e, c, max_steps=n, split=0.7 * scale)
            s0, F0, L0, why0 = run(word, beta, [0.0] * 3, c, max_steps=n)
            V1, V0 = vectors_by_label(F1, L1), vectors_by_label(F0, L0)
            Fi, Li = make_front(word, beta, e, 0.7 * scale)
            Vi = vectors_by_label(Fi, Li)
            out = []
            for a, bb in ((1, 0), (2, 0), (101, 100)):
                r0 = Vi[a] / Vi[bb]
                rf, rl = V1[a] / V1[bb], V0[a] / V0[bb]
                out.append(f"{a}/{bb}: {(rf - rl) / (r0 - 1):.4f}")
            print(f"  c={c:+.5f} steps={s1}/{s0} stop={why1}/{why0}  K=" + "  ".join(out))
