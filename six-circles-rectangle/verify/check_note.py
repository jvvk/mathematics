"""Independent check of every claim in the Gazette note, at 50 digits. Writes coords.json for the figures."""
import json, os, sys
import mpmath as mp
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from config import sol
mp.mp.dps = 50
a, b, c, w, x = sol(); h = mp.mpf(1)
P = lambda X, Y: (mp.mpf(X), mp.mpf(Y))
O = P(0, 0); A = (-(w - a), h - a); B = (x, h - b); C = (w - c, h - c)
Ap, Bp, Cp = (-A[0], -A[1]), (-B[0], -B[1]), (-C[0], -C[1])
At, Bt, Ct, U = (A[0], h), (B[0], h), (C[0], h), (mp.mpf(0), h)
M = ((At[0] + Ct[0]) / 2, h)
d = lambda p, q: mp.sqrt((p[0] - q[0])**2 + (p[1] - q[1])**2)
sub = lambda p, q: (p[0] - q[0], p[1] - q[1])
dot = lambda u, v: u[0]*v[0] + u[1]*v[1]
cross = lambda u, v: u[0]*v[1] - u[1]*v[0]
ang = lambda p, q, r: mp.acos(dot(sub(p, q), sub(r, q)) / (d(p, q) * d(r, q)))   # angle at q
T = (A[0] + a*(Cp[0]-A[0])/d(A, Cp), A[1] + a*(Cp[1]-A[1])/d(A, Cp))
Cb = (Cp[0], -h)
S = ((A[0] + Cp[0]) / 2, (A[1] + Cp[1]) / 2); S0 = (S[0], mp.mpf(0))
tE = A[1] / (A[1] - Cp[1]); E = (A[0] + tE*(Cp[0]-A[0]), mp.mpf(0))
m = sub(M, O); k = dot(U, m) / dot(m, m); K = (2*k*m[0] - U[0], 2*k*m[1] - U[1])
psi = ang(U, O, Bt)
tol = mp.mpf(10)**-40
checks = {
 "tangencies AB, BC, CA', BA', OB=b": max(abs(d(A,B)-a-b), abs(d(B,C)-b-c), abs(d(C,Ap)-a-c), abs(d(B,Ap)-a-b), abs(d(B,O)-b)) < tol,
 "a,b,c < h": max(a, b, c) < h,
 "BA = BA'": abs(d(B,A) - d(B,Ap)) < tol,
 "OA perp OB": abs(dot(sub(A,O), sub(B,O))) < tol,
 "angle UOB = 2 psi": abs(ang(U,O,B) - 2*psi) < tol,
 "Bt right of U": Bt[0] > U[0],
 "sqrt a + sqrt c = sqrt 2h": abs(mp.sqrt(a)+mp.sqrt(c)-mp.sqrt(2*h)) < tol,
 "AtCt = 2 sqrt b (sqrt a + sqrt c)": abs(d(At,Ct) - 2*mp.sqrt(b)*(mp.sqrt(a)+mp.sqrt(c))) < tol,
 "OBt^2 = 2bh": abs(d(O,Bt)**2 - 2*b*h) < tol,
 "AtCt = 2 OBt": abs(d(At,Ct) - 2*d(O,Bt)) < tol,
 "U->M = (a-c)/2": abs((M[0]-U[0]) - (a-c)/2) < tol,
 "M->Bt = sqrt b (sqrt a - sqrt c)": abs((Bt[0]-M[0]) - mp.sqrt(b)*(mp.sqrt(a)-mp.sqrt(c))) < tol,
 "a > c, order U, M, Bt": a > c and U[0] < M[0] < Bt[0],
 "UM/MBt = OU/OBt": abs(d(U,M)/d(M,Bt) - d(O,U)/d(O,Bt)) < tol,
 "OM bisects UOBt": abs(ang(U,O,M) - psi/2) < tol,
 "At, T, C'b collinear": abs(cross(sub(T,At), sub(Cb,At))) < tol,
 "At->C'b = -2 (O->M)": abs(Cb[0]-At[0] + 2*M[0]) < tol and abs(Cb[1]-At[1] + 2*M[1]) < tol,
 "AtT parallel OM": abs(cross(sub(T,At), m)) < tol,
 "AC' parallel OBt": abs(cross(sub(Cp,A), sub(Bt,O))) < tol,
 "OS0 = OBt": abs(d(O,S0) - d(O,Bt)) < tol,
 "SS0 = UM": abs(d(S,S0) - d(U,M)) < tol,
 "S0 left of O, S below S0": S0[0] < 0 and S[1] < S0[1],
 "K on OBt, between O and Bt": abs(cross(sub(K,O), sub(Bt,O))) < tol and 0 < dot(sub(K,O), sub(Bt,O)) < dot(sub(Bt,O), sub(Bt,O)),
 "OK = h, MK = MU, MK perp OBt": abs(d(O,K)-h) < tol and abs(d(M,K)-d(M,U)) < tol and abs(dot(sub(K,M), sub(Bt,O))) < tol,
 "angle KMBt = psi = angle S0SE' (at M and S)": abs(ang(K,M,Bt) - psi) < tol and abs(ang(S0,S,E) - psi) < tol,
 "angles at Bt and E' = 90 - psi": abs(ang(M,Bt,K) - (mp.pi/2-psi)) < tol and abs(ang(S,E,S0) - (mp.pi/2-psi)) < tol,
 "S0E' = KBt = OBt - h": abs(d(S0,E) - d(K,Bt)) < tol and abs(d(K,Bt) - (d(O,Bt)-h)) < tol,
 "E' right of S0, E' = (-h, 0)": E[0] > S0[0] and abs(E[0] + h) < tol,
 "angle E'OA = 2 psi": abs(ang(E,O,A) - 2*psi) < tol,
 "angle OE'A = 90 - psi": abs(ang(O,E,A) - (mp.pi/2 - psi)) < tol,
 "angle OAE' = 90 - psi": abs(ang(O,A,E) - (mp.pi/2 - psi)) < tol,
 "OA = h, AA' = 2h": abs(d(O,A) - h) < tol and abs(d(A,Ap) - 2*h) < tol,
}
for k_, v in checks.items(): print("PASS" if v else "FAIL", k_)
print("psi (deg) =", mp.nstr(psi*180/mp.pi, 12), " a b c w =", [mp.nstr(t, 12) for t in (a, b, c, w)])
pts = dict(O=O, A=A, B=B, C=C, Ap=Ap, Bp=Bp, Cp=Cp, At=At, Bt=Bt, Ct=Ct, U=U, M=M, T=T, Cb=Cb, S=S, S0=S0, E=E, K=K)
json.dump({"h": 1, "w": float(w), "r": {"a": float(a), "b": float(b), "c": float(c)},
           "pts": {k_: [float(p[0]), float(p[1])] for k_, p in pts.items()}}, open(os.path.join(os.path.dirname(os.path.abspath(__file__)), "coords.json"), "w"), indent=1)
sys.exit(0 if all(checks.values()) else 1)
