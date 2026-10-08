"""Limit model for a general convex polygon K (smallest enclosing SIMILAR copy: scale 1+eps, rotation Theta/n, shift C/n).
Side i: outward normal u_i, support h_i, tangent t_i = R90 u_i, side = {s in [a_i, b_i]} with s = x.t_i.
Points on side i: Poisson (intensity 1) in (s, D), D = n*depth. Enclosing: eps h_i + C.u_i >= Theta s - D for all points.
Minimise eps (LP). Copy inside K  <=>  eps h_i + C.u_i <= min(Theta a_i, Theta b_i) for all i (vertex poke-out).
Usage: general_K.py name trials seed [Dmax]"""
import os, sys, signal, math, numpy as np
from scipy.optimize import linprog
def _stop(*_): raise TimeoutError
signal.signal(signal.SIGALRM, _stop); signal.alarm(int(os.environ.get("TIME_LIMIT", "0")))
SHAPES = {
    "equilateral": np.array([[0, 0], [1, 0], [0.5, math.sqrt(3) / 2]]),
    "tri_30_60_90": np.array([[0, 0], [math.sqrt(3), 0], [0, 1.0]]),
    "tri_20_40_120": None, "tri_80_60_40": None,
    "square": np.array([[0, 0], [1, 0], [1, 1], [0, 1.0]]),
    "rect_2x1": np.array([[0, 0], [2, 0], [2, 1], [0, 1.0]]),
    "rhombus_60": np.array([[0, 0], [1, 0], [1.5, math.sqrt(3) / 2], [0.5, math.sqrt(3) / 2]]),
    "pentagon_irreg": np.array([[0, 0], [2, 0], [2.6, 1.2], [1.2, 2.2], [-0.3, 1.1]]),
}
def tri_angles(A, B):   # vertices (0,0), (1,0), apex from angles A at origin and B at (1,0)
    ta, tb = math.tan(math.radians(A)), math.tan(math.radians(B)); x = tb / (ta + tb); return np.array([[0, 0], [1, 0], [x, x * ta]])
SHAPES["tri_20_40_120"] = tri_angles(20, 40); SHAPES["tri_80_60_40"] = tri_angles(80, 60)
SHAPES["hexagon"] = np.array([[math.cos(math.pi*k/3), math.sin(math.pi*k/3)] for k in range(6)])
SHAPES["parallelogram"] = np.array([[0, 0], [2, 0], [2.7, 1], [0.7, 1.0]])
SHAPES["trapezoid"] = np.array([[0, 0], [3, 0], [2, 1.2], [0.6, 1.2]])
SHAPES["hex_cs_irreg"] = np.array([[0, 0], [2, -0.3], [3, 0.8], [2.6, 2.0], [0.6, 2.3], [-0.4, 1.2]])
def sides(V):
    V = V - V.mean(0); out = []
    d1, d2 = V[1] - V[0], V[2] - V[0]
    if d1[0] * d2[1] - d1[1] * d2[0] < 0: V = V[::-1]
    for i in range(len(V)):
        P, Q = V[i], V[(i + 1) % len(V)]; t = (Q - P) / np.linalg.norm(Q - P); u = np.array([t[1], -t[0]])
        out.append((u, P @ u, P @ t, Q @ t))
    return out
def trial(S, rng, Dmax):
    rows = []; rhs = []
    for (u, h, a, b) in S:
        m = rng.poisson(Dmax * (b - a)); D = rng.uniform(0, Dmax, m); s = rng.uniform(a, b, m)
        for Di, si in zip(D, s): rows.append([-h, -u[0], -u[1], si]); rhs.append(Di)   # -(eps h + C.u - Theta s) <= D
    A = np.array(rows); bb = np.array(rhs)
    r = linprog([1, 0, 0, 0], A_ub=A, b_ub=bb, bounds=[(None, None)] * 4, method="highs"); eps = r.x[0]
    for sg in (1, -1):   # vars (C, Theta) with eps fixed; event rows: h eps + C.u - Theta*(a or b) <= 0
        ev = [[u[0], u[1], -(a if sg == 1 else b)] for (u, h, a, b) in S]; evb = [-h * eps for (u, h, a, b) in S]
        A2 = np.r_[A[:, 1:], np.array(ev)]; b2 = np.r_[bb - A[:, 0] * eps, evb]
        r2 = linprog([0, 0, 0], A_ub=A2, b_ub=b2 + 1e-9, bounds=[(None, None), (None, None), (0, None) if sg == 1 else (None, 0)], method="highs")
        if r2.status == 0: return True
    return False
if __name__ == "__main__":
    name, T, seed = sys.argv[1], int(sys.argv[2]), int(sys.argv[3]); Dmax = float(sys.argv[4]) if len(sys.argv) > 4 else 25.0
    S = sides(SHAPES[name]); area = 0.5 * sum(L * h for (u, h, a, b) in S for L in [b - a])
    # rescale to unit area so Dmax means the same thing for every shape
    k = 1 / math.sqrt(area); S = [(u, h * k, a * k, b * k) for (u, h, a, b) in S]
    rng = np.random.default_rng(seed); res = []
    try:
        for _ in range(T): res.append(trial(S, rng, Dmax))
    except Exception as e: print("stopped:", type(e).__name__)
    m = np.mean(res); print(f"{name}: trials={len(res)} P={m:.4f} +- {math.sqrt(m*(1-m)/len(res)):.4f}")
