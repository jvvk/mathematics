"""Controls: P' = I ⋆ Sym²(D') for Zagier's modular sporadic D'. Sym²(D') recurrence guessed from f'^2,
then Hadamard with binom(2n,n); compute instanton numbers and report integrality to d = DM."""
import sys
import sympy as sp
from fractions import Fraction as F
import cyk

DM = int(sys.argv[1]) if len(sys.argv) > 1 else 14
n = sp.symbols("n")


def zagier_seq(A, B, lam, N):
    u = [F(1), F(lam)]
    for k in range(1, N):
        u.append(((A * k * (k + 1) + lam) * u[k] - B * k * k * u[k - 1]) / (k + 1) ** 2)
    return u


def guess3(w, N):
    """Find (n+1)^3 w_{n+1} = R1(n) w_n - R2(n) w_{n-1} with deg R1, R2 <= 3."""
    c = sp.symbols("c0:8")
    eqs = []
    for k in range(1, N):
        R1 = sum(c[i] * k**i for i in range(4)); R2 = sum(c[4 + i] * k**i for i in range(4))
        eqs.append((k + 1)**3 * w[k + 1] - R1 * w[k] + R2 * w[k - 1])
    sol = sp.solve(eqs, c, dict=True)
    if not sol:
        return None
    s = sol[0]
    R1 = sp.factor(sum(s.get(c[i], 0) * n**i for i in range(4)))
    R2 = sp.factor(sum(s.get(c[4 + i], 0) * n**i for i in range(4)))
    return R1, R2


cases = {"A": (7, -8, 2), "B": (9, 27, 3), "C": (10, 9, 3), "D": (11, -1, 3), "E": (12, 32, 4), "F": (17, 72, 6)}
for name, (A, B, lam) in cases.items():
    f = zagier_seq(A, B, lam, 40)
    w = [sum(f[i] * f[k - i] for i in range(k + 1)) for k in range(41)]
    g = guess3(w, 30)
    if g is None:
        print(name, "no 3-term Sym^2 recurrence of this shape"); continue
    R1, R2 = g
    if sp.rem(sp.Poly(R2, n), sp.Poly(n, n)).as_expr() != 0:
        print(name, "R2 not divisible by n:", R2); continue
    Qs = cyk.hadamard_I(R1, R2)
    y0, q, K = cyk.yukawa(Qs, DM)
    nd = cyk.instantons(K, DM)
    ok_y = all(v.denominator == 1 for v in y0); ok_q = all(v.denominator == 1 for v in q)
    ok_K = all(v.denominator == 1 for v in K); bad = [d for d in range(1, DM + 1) if nd[d].denominator != 1]
    print(f"{name} {A,B,lam}: R1={R1}, R2={R2} | y0 int {ok_y}, q int {ok_q}, K int {ok_K}, "
          f"n_d non-integral at d={bad[:6]}  n1..4={[str(v) for v in nd[1:5]]}")

# the strange operator itself, through the same pipeline
R1 = 4 * (2*n + 1) * (5*n**2 + 5*n + 2); R2 = 48 * n * (9*n**2 - 1)
y0, q, K = cyk.yukawa(cyk.hadamard_I(R1, R2), DM)
nd = cyk.instantons(K, DM)
print("strange: n_d non-integral at", [d for d in range(1, DM + 1) if nd[d].denominator != 1][:6], [str(v) for v in nd[1:4]])
