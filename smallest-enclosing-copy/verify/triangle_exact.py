"""Exact limit probability for a general triangle (no Monte Carlo; 2-D quadrature of a piecewise quadratic):
P = 2 sum_k I_k / (Q L1 L2 L3),  Q = sum L_i^2 / 2,
I_k = (L_k/2) int_{side i} int_{side j} (x - a_k)(b_k - x)_+ ds_i ds_j,  x = -(L_i s_i + L_j s_j)/L_k.
Usage: triangle_exact.py A B   (angles in degrees)   or   import P_angles"""
import sys, math, numpy as np
import general_K as G
def P_angles(A, B, n=1601):
    S = G.sides(G.tri_angles(A, B)); L = np.array([b - a for (u, h, a, b) in S]); a_ = np.array([s[2] for s in S]); b_ = np.array([s[3] for s in S])
    tot = 0.0
    for k in range(3):
        i, j = [q for q in range(3) if q != k]
        si = np.linspace(a_[i], b_[i], n); sj = np.linspace(a_[j], b_[j], n); SI, SJ = np.meshgrid(si, sj, indexing="ij")
        x = -(L[i] * SI + L[j] * SJ) / L[k]; f = np.clip((x - a_[k]) * (b_[k] - x), 0, None)
        tot += L[k] / 2 * np.trapezoid(np.trapezoid(f, sj, axis=1), si)
    Q = (L ** 2).sum() / 2; return 2 * tot / (Q * L.prod())
if __name__ == "__main__":
    A, B = float(sys.argv[1]), float(sys.argv[2]); print(f"triangle {A},{B},{180-A-B}: P = {P_angles(A, B):.6f}")
