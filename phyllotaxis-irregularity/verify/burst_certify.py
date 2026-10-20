"""Item (C): certify the step-2 burst in the regime |c| << |eps| << 1 (c -> 0 first).

Front: the (3,2) word current when the first down reaches threshold, with lineage offsets frozen by Prop 2:
Ua-lineage vectors (Ua/+, Ua/-) at +eps/2, Ub-lineage (Ub/+, Ub/-) and D (child-parallel to Ub/-) at -eps/2;
ups at angle u + off, downs at d(u) + off, d(u) fixed by vertical closure. u is lowered (the shrinking drift) until
the first notch hinge reaches 120 deg + eta, eta << eps. Then constant-diameter stacking (c = 0) is run in interval
arithmetic. Each decision (which location is lowest) is certified with its margin reported in units of eps:
margins must be >= k*eps (robust to the O(c) per-step terms), not O(eta).
"""
from __future__ import annotations
import os, sys
from mpmath import mp, iv, mpf, sin, cos, pi, findroot
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
mp.dps = 50; iv.dps = 50

def deg(x): return x * pi / 180

def build(word, u, eps):
    off = {"Ua/+": eps / 2, "Ua/-": eps / 2, "Ub/+": -eps / 2, "Ub/-": -eps / 2, "D": -eps / 2}
    ups = [w for w in word if w.endswith("/+")]
    downs = [w for w in word if not w.endswith("/+")]
    f = lambda d: sum(sin(u + off[w]) for w in ups) + sum(sin(d + off[w]) for w in downs)
    d = findroot(f, deg(-23.4))
    ang = {w: (u + off[w]) if w.endswith("/+") else (d + off[w]) for w in word}
    return [ang[w] for w in word]

def hinges(angles):
    N = len(angles); out = []
    for k in range(N):
        a, b = angles[k], angles[(k + 1) % N]
        if sin(a) < 0 and sin(b) > 0:
            out.append((pi - (b - a), k))
    return out

def at_threshold(word, eps, eta):
    g = lambda u: max(h for h, _ in hinges(build(word, u, eps))) - (deg(120) + eta)
    lo, hi = deg(40), deg(33)  # g(lo) < 0 (before threshold), g(hi) > 0
    assert g(lo) < 0 < g(hi)
    for _ in range(200):
        m = (lo + hi) / 2
        lo, hi = (m, hi) if g(m) < 0 else (lo, m)
    return build(word, hi, eps)

# ---- interval geometry (independent of the simulators) ----
def ivp(x): return iv.mpf(x)
def apex(P, R):
    dx, dy = R[0] - P[0], R[1] - P[1]; L2 = dx * dx + dy * dy
    if not (L2.b < 4): return None
    k = iv.sqrt(1 / L2 - iv.mpf(1) / 4)
    return ((P[0] + R[0]) / 2 - k * dy, (P[1] + R[1]) / 2 + k * dx)

def step(pts, names, L):
    N = len(pts); cands = []
    for a in range(N):
        for gap in range(0, N - 1):
            b = a + gap + 1; R = pts[b % N] if b < N else (pts[b % N][0] + L, pts[b % N][1])
            Q = apex(pts[a], R)
            if Q is None: continue
            ok = True
            for k in range(N):
                if k in (a, b % N): continue
                for sh in (-1, 0, 1):
                    dd = (Q[0] - pts[k][0] - sh * L) ** 2 + (Q[1] - pts[k][1]) ** 2
                    if dd.b < 1: ok = False; break
                    if dd.a < 1: ok = "TIE"
                if ok is False: break
            if ok is not False:
                cands.append((Q, a, gap, ok))
    # group into locations by x (within half a diameter, periodic)
    locs = []
    for c in sorted(cands, key=lambda t: t[0][1].a):
        for L_ in locs:
            dx = abs(((float(c[0][0].a) - float(L_[0][0][0].a)) + L / 2) % L - L / 2)
            if dx < 0.5: L_.append(c); break
        else:
            locs.append([c])
    locs.sort(key=lambda l: l[0][0][1].a)
    low, nxt = locs[0], locs[1]
    margin = nxt[0][0][1] - low[0][0][1]
    Q, a, gap, ok = low[0]
    # apply: remove disks strictly between parents, insert Q after a
    rem = {(a + t + 1) % N for t in range(gap)}
    newpts = []; newnames = []
    for k in range(N):
        if k in rem: continue
        newpts.append(pts[k]); newnames.append(names[k])
        if k == a:
            newpts.append(Q); newnames.append("new")
    # re-sort by x modulo L, keep order cyclic
    pairs = sorted(zip(newpts, newnames), key=lambda t: (float(t[0][0].a) % L))
    return [p for p, _ in pairs], [n for _, n in pairs], "TRP"[min(gap, 2)] + ("H" if gap > 2 else ""), margin, len(low)

def run(word, eps, eta, max_events=5):
    ang = at_threshold(word, eps, eta)
    pts = [(ivp(0), ivp(0))]
    for t in ang[:-1]:
        pts.append((pts[-1][0] + iv.cos(ivp(t)), pts[-1][1] + iv.sin(ivp(t))))
    L = float((sum(cos(t) for t in ang)))
    names = list(word); events = []
    for _ in range(max_events):
        pts, names, ev, margin, nloc = step(pts, names, L)
        events.append((ev, float(margin.a) / float(eps)))
        if ev == "P": break
    return events

if __name__ == "__main__":
    cycle = ["Ua/+ Ua/- Ub/+ D Ub/-", "Ua/+ Ub/- Ua/- Ub/+ D", "Ua/+ Ub/- Ub/+ Ua/- D",
             "Ua/+ D Ub/- Ub/+ Ua/-", "Ua/+ D Ub/+ Ub/- Ua/-", "Ua/+ Ua/- D Ub/+ Ub/-"]
    for eps in (mpf("1e-4"), mpf("1e-6")):
        for w in cycle:
            ev = run(w.split(), eps, eps * mpf("1e-6"))
            print(f"eps={mp.nstr(eps,2)} start [{w}]: " + "  ".join(f"{e}(margin {m:.3f} eps)" for e, m in ev), flush=True)
