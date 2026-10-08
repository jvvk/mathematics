"""General-K formula (no parallel sides): P(K) = V(K) * T(K), unit-area K, intensity 1.
V(K) = int dTheta int dt e^{-2 t} Area{C : C.u_i <= t h_i + min(Theta a_i, Theta b_i)}   (t = -eps >= 0)
T(K) = (1/24) (sum L_i)^4 E[|det A| 1{e_1 in cone(rows)}], rows (h_i, u_i, -s_i), side ~ length, s uniform on side.
Usage: formula_K.py name samples seed"""
import os, sys, signal, math, numpy as np
import general_K as G
def _stop(*_): raise TimeoutError
signal.signal(signal.SIGALRM, _stop); signal.alarm(int(os.environ.get("TIME_LIMIT", "0")))
name, N, seed = sys.argv[1], int(sys.argv[2]), int(sys.argv[3]); rng = np.random.default_rng(seed)
S = G.sides(G.SHAPES[name]); A0 = 0.5 * sum((b - a) * h for (u, h, a, b) in S); k = 1 / math.sqrt(A0)
S = [(u, h * k, a * k, b * k) for (u, h, a, b) in S]; U = np.array([s[0] for s in S]); H = np.array([s[1] for s in S])
Aa = np.array([s[2] for s in S]); Bb = np.array([s[3] for s in S]); L = Bb - Aa
def poly_area(sup):   # area of {C : C.u_i <= sup_i}, by clipping a big square
    P = [np.array(v) for v in ([-50, -50], [50, -50], [50, 50], [-50, 50])]
    for u, c in zip(U, sup):
        Q = []
        for i in range(len(P)):
            X, Y = P[i], P[(i + 1) % len(P)]; fx, fy = X @ u - c, Y @ u - c
            if fx <= 0: Q.append(X)
            if fx * fy < 0: Q.append(X + (Y - X) * fx / (fx - fy))
        P = Q
        if len(P) < 3: return 0.0
    x = np.array([p[0] for p in P]); y = np.array([p[1] for p in P]); return 0.5 * abs(x @ np.roll(y, -1) - y @ np.roll(x, -1))
th = np.linspace(-3, 3, 241); ts = np.linspace(0, 8, 321)
F = np.array([[math.exp(-2 * t) * poly_area(t * H + np.minimum(T * Aa, T * Bb)) for t in ts] for T in th])
V = np.trapezoid(np.trapezoid(F, ts, axis=1), th)
tot = 0.0; done = 0; pside = L / L.sum()
while done < N:
    m = min(200000, N - done); idx = rng.choice(len(S), (m, 4), p=pside); s = Aa[idx] + rng.uniform(0, 1, (m, 4)) * L[idx]
    M = np.stack([H[idx], U[idx][..., 0], U[idx][..., 1], -s], -1); det = np.linalg.det(M); g = np.abs(det) > 1e-12
    lam = np.zeros((m, 4)); lam[g] = np.linalg.solve(np.transpose(M[g], (0, 2, 1)), np.tile([1., 0, 0, 0], (g.sum(), 1))[..., None])[..., 0]
    tot += np.where(g & (lam >= 0).all(1), np.abs(det), 0).sum(); done += m
T_ = L.sum() ** 4 / 24 * tot / done
print(f"{name}: V={V:.6f} T={T_:.4f} P=V*T={V*T_:.4f}")
