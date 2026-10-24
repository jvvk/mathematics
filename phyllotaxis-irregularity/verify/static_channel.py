"""Below the window: on H the channel condition mu_Z > 0 follows from validity (mu_Z = notch clearance + ridge
clearance + sqrt3 q k_u). It can fail on a valid front only when another hinge inside a run is perturbed too.
Here the hinge between U2 and U3 is 180 + zeta (fronts with n >= 3), the ridge takes up the rest. Prediction:
valid front with mu_Z < 0 (2s + a - e < -2 q k_u, first order) => no disk fits near Q0 and the first disk is not
a pentagon; with mu_Z > 0 and mu_C > 0 => pentagon."""
from __future__ import annotations
import math, os, sys
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from independent_stack import Stack
import static_general as G

def build(m, n, alpha, sigma, eps, zeta, cc):
    u = G.bearing_u(m, n); bD = u - 2 * math.pi / 3
    rel = [alpha] * (m - 1) + [0.0] + [2 * math.pi / 3 - sigma, 2 * math.pi / 3 - sigma + eps]
    rel += [2 * math.pi / 3 - sigma + eps - zeta] * (n - 2)
    N = m + n; phi, ys = 0.0, [0.0] * N
    for _ in range(100):
        Ls = [1 + cc * (ys[k] + ys[(k + 1) % N]) / 2 for k in range(N)]
        for _ in range(50):
            f = sum(Ls[k] * math.sin(bD + phi + rel[k]) for k in range(N))
            g = sum(Ls[k] * math.cos(bD + phi + rel[k]) for k in range(N))
            phi -= f / g
        pts = [(0.0, 0.0)]
        for k in range(N - 1):
            a = bD + phi + rel[k]
            pts.append((pts[-1][0] + Ls[k] * math.cos(a), pts[-1][1] + Ls[k] * math.sin(a)))
        ys = [p[1] for p in pts]
    lam = sum(Ls[k] * math.cos(bD + phi + rel[k]) for k in range(N))
    return [(x, y, 1 + cc * y) for x, y in pts], lam

def valid(disks, lam):
    N = len(disks)
    for i in range(N):
        for j in range(N):
            for sh in (-1, 0, 1):
                if (i == j and sh == 0) or (abs(i - j) == 1 and sh == 0) or ({i, j} == {0, N - 1} and sh != 0 and (j - i) * sh < 0):
                    continue
                d = math.hypot(disks[j][0] + sh * lam - disks[i][0], disks[j][1] - disks[i][1])
                if d < (disks[i][2] + disks[j][2]) / 2 - 1e-12:
                    return False
    return True

if __name__ == "__main__":
    t = 2e-3
    bad = 0
    for (m, n) in ((2, 3), (3, 4), (4, 5)):
        u = G.bearing_u(m, n); ku = math.cos(u - math.pi / 3)
        for (a, s, e, z, q) in ((0, 0.3, 1, 1, 0.05), (0, 0.4, 1, 1, 0.05), (0, 0.7, 1, 1, 0.05), (0, 0.8, 1, 0.5, 0.05)):
            disks, lam = build(m, n, a * t, s * t, e * t, z * t, -q * t)
            ok = valid(disks, lam)
            muZ = math.sqrt(3) / 2 * (2 * s + a - e) + math.sqrt(3) * q * ku
            muC = math.sqrt(3) / 2 * (e - s) - q / 8 * (3 * math.sin(u) + 5 * math.sqrt(3) * math.cos(u))
            S = Stack([(x / lam, y / lam, d / lam) for x, y, d in disks], 1 / lam, -q * t, tol=1e-13)
            p0 = S.parastichy(); dl = S.step()
            ev = {1: "T", 0: "R", -1: "P"}.get(dl, dl)
            pred = "P" if (muZ > 0 and muC > 0) else ("R" if muC < 0 else "not P")
            agree = ev in ("T", "R") if pred == "not P" else ev == pred
            print(f"({m},{n}) a,s,e,zeta,q={a,s,e,z,q}: valid={ok} mu_C={muC:+.3f} mu_Z={muZ:+.3f} predicted {pred}, simulated {ev} {p0}->{S.parastichy()} {'ok' if agree else 'MISMATCH'}")
            if not ok or not agree:
                bad += 1
                reason = "invalid front" if not ok else f"predicted {pred}, simulated {ev}"
                print(f"FAIL: ({m},{n}) a,s,e,zeta,q={a,s,e,z,q}: {reason}")
    print(f"{'FAIL' if bad else 'PASS'}: 12 channel comparisons, {bad} failures")
    sys.exit(1 if bad else 0)
