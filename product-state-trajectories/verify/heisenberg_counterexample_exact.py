"""Exact verification: Heisenberg exchange in a uniform field keeps the entanglement of psi0 constant, but the
trajectory has no time-independent local generator.

H = (XX + YY + ZZ)/2 - (Z1 + Z2)/2 + 3/2,  psi0 = -|00> + (1+i)|01> + (i-1)|10> + |11>  (norm^2 = 6).
"""
import sys

import sympy as sp

failures = []


def check(label, ok):
    print(label, ok)
    if ok is not True:
        failures.append(label)

t = sp.symbols("t", real=True)
I = sp.I
X = sp.Matrix([[0, 1], [1, 0]]); Y = sp.Matrix([[0, -I], [I, 0]]); Z = sp.Matrix([[1, 0], [0, -1]]); E = sp.eye(2)
kp = sp.kronecker_product
H = (kp(X, X) + kp(Y, Y) + kp(Z, Z)) / 2 - (kp(Z, E) + kp(E, Z)) / 2 + sp.Rational(3, 2) * sp.eye(4)
psi0 = sp.Matrix([-1, 1 + I, I - 1, 1])  # basis |00>,|01>,|10>,|11>

# exact evolution via the spectral decomposition
vals = H.eigenvals()
print("spectrum of H:", vals)
U = sp.simplify((-I * H * t).exp())
psi = sp.simplify(U * psi0)
M = sp.Matrix([[psi[0], psi[1]], [psi[2], psi[3]]])
z = sp.exp(-I * t)
expected = sp.Matrix([[-z, 1 + I * z**2], [I * z**2 - 1, z**3]])
check("M(t) == [[-z, 1+iz^2],[iz^2-1, z^3]]:", sp.simplify(M - expected) == sp.zeros(2, 2))
check("det M(t) == 1:", sp.simplify(M.det()) == 1)
check("||M(t)||^2 == 6:", sp.simplify(sum(sp.Abs(e) ** 2 for e in M).rewrite(sp.cos)) == 6)
# components by frequency and their orthogonality
comps = {0: sp.Matrix([0, 1, -1, 0]), 1: sp.Matrix([-1, 0, 0, 0]), 2: sp.Matrix([0, I, I, 0]), 3: sp.Matrix([0, 0, 0, 1])}
check("psi(t) == sum_mu e^{-i mu t} V_mu:", sp.simplify(psi - sum((sp.exp(-I * m * t) * v for m, v in comps.items()), sp.zeros(4, 1))) == sp.zeros(4, 1))
check("H V_mu == mu V_mu:", all(sp.simplify(H * v - m * v) == sp.zeros(4, 1) for m, v in comps.items()))
check("V_mu pairwise orthogonal:", all(sp.simplify((comps[a].H * comps[b])[0]) == 0 for a in comps for b in comps if a < b))
# Schmidt coefficients from det and norm: s1^2 s2^2 = |det|^2 / norm^4 = 1/36, s1^2 + s2^2 = 1
s = sp.symbols("s", positive=True)
print("normalised Schmidt coefficients^2:", sp.solve(sp.Eq(s * (1 - s), sp.Rational(1, 36)), s), " concurrence = 2|det|/norm^2 =", sp.Rational(2, 6))

print("ALL PASS" if not failures else f"FAIL: {failures}")
sys.exit(1 if failures else 0)
