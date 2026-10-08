"""General convex polygon K, parallel sides allowed (unit area, intensity 1):
P(K) = V(K) T_nd(K) + sum over ordered parallel pairs (k pair side, kb opposite) of P_deg(k),
T_nd: tetrahedron average EXCLUDING tuples with two points on k and one on its parallel opposite kb (0 on a face),
P_deg(k) = sigma_k int dTheta int dt e^{-2t} w_k [ width_{u_k} R + S_k Area R ],  R = {C : C.u_j <= t h_j + m_j(Theta)},
sigma_k = int over the overlap of side k with the projection of kb of (s-a)(b-s)(b-a)/2 ds,
S_k = sum_{j : u_j.t_k > 0} L_j u_j.t_k,  w_k = h_k + h_kb.   Usage: formula_par.py name samples seed"""
import os, sys, signal, math, numpy as np
import general_K as G
def _stop(*_): raise TimeoutError
signal.signal(signal.SIGALRM, _stop); signal.alarm(int(os.environ.get("TIME_LIMIT", "0")))
name, N, seed = sys.argv[1], int(sys.argv[2]), int(sys.argv[3]); rng = np.random.default_rng(seed)
S = G.sides(G.SHAPES[name]); A0 = 0.5 * sum((b - a) * h for (u, h, a, b) in S); k0 = 1 / math.sqrt(A0)
S = [(u, h * k0, a * k0, b * k0) for (u, h, a, b) in S]; m = len(S)
U = np.array([s[0] for s in S]); H = np.array([s[1] for s in S]); Aa = np.array([s[2] for s in S]); Bb = np.array([s[3] for s in S]); L = Bb - Aa
T_ = np.c_[-U[:, 1], U[:, 0]]   # t_i = R90 u_i
opp = {i: j for i in range(m) for j in range(m) if i != j and np.allclose(U[i], -U[j], atol=1e-9)}
def clip(sup):
    P = [np.array(v, float) for v in ([-60, -60], [60, -60], [60, 60], [-60, 60])]
    for u, c in zip(U, sup):
        Q = []
        for i in range(len(P)):
            X, Y = P[i], P[(i + 1) % len(P)]; fx, fy = X @ u - c, Y @ u - c
            if fx <= 0: Q.append(X)
            if fx * fy < 0: Q.append(X + (Y - X) * fx / (fx - fy))
        P = Q
        if len(P) < 3: return None
    return np.array(P)
def area(P): return 0.0 if P is None else 0.5 * abs(P[:, 0] @ np.roll(P[:, 1], -1) - P[:, 1] @ np.roll(P[:, 0], -1))
th = np.linspace(-8, 8, 321); ts = np.linspace(0, 14, 281)
polys = [[clip(t * H + np.minimum(T * Aa, T * Bb)) for t in ts] for T in th]
V = np.trapezoid(np.trapezoid([[math.exp(-2 * t) * area(P) for t, P in zip(ts, row)] for row in polys], ts, axis=1), th)
# nondegenerate tetrahedron average
tot = 0.0; done = 0; ps = L / L.sum()
while done < N:
    n_ = min(200000, N - done); idx = rng.choice(m, (n_, 4), p=ps); s = Aa[idx] + rng.uniform(0, 1, (n_, 4)) * L[idx]
    M = np.stack([H[idx], U[idx][..., 0], U[idx][..., 1], -s], -1); det = np.linalg.det(M); g = np.abs(det) > 1e-12
    lam = np.zeros((n_, 4)); lam[g] = np.linalg.solve(np.transpose(M[g], (0, 2, 1)), np.tile([1., 0, 0, 0], (g.sum(), 1))[..., None])[..., 0]
    deg = np.zeros(n_, bool)
    for kk, kb in opp.items(): deg |= ((idx == kk).sum(1) >= 2) & ((idx == kb).sum(1) >= 1)
    tot += np.where(g & (lam >= 0).all(1) & ~deg, np.abs(det), 0).sum(); done += n_
Tnd = L.sum() ** 4 / 24 * tot / done
Pdeg = 0.0
for kk, kb in opp.items():
    a, b = Aa[kk], Bb[kk]; lo, hi = max(a, -Bb[kb]), min(b, -Aa[kb])     # projection of kb onto t_k is [-b_kb, -a_kb]
    xs = np.linspace(lo, hi, 2001) if hi > lo else np.array([0.0])
    sig = np.trapezoid((xs - a) * (b - xs) * (b - a) / 2, xs) if hi > lo else 0.0
    c = U @ T_[kk]; Sk = (L * np.clip(c, 0, None)).sum(); wk = H[kk] + H[kb]
    def term(P):
        if P is None: return 0.0
        proj = P @ U[kk]; return (proj.max() - proj.min()) + Sk * area(P)
    Pdeg += sig * wk * np.trapezoid(np.trapezoid([[math.exp(-2 * t) * term(P) for t, P in zip(ts, row)] for row in polys], ts, axis=1), th)
print(f"{name}: V*T_nd={V*Tnd:.4f} deg={Pdeg:.4f} total={V*Tnd+Pdeg:.4f}  (parallel pairs: {len(opp)//2})")
