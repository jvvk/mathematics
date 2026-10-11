"""Controls: P' = I ⋆ L' for known third-order Apéry-like sequences L' (all symmetric squares of modular
second-order operators). Recurrence guessed from terms, then Hadamard with binom(2n,n)."""
import sys
import sympy as sp
from math import comb, factorial as fac
import cyk
from controls import guess3

DM = int(sys.argv[1]) if len(sys.argv) > 1 else 14
n = sp.symbols("n")
C = comb
seqs = {
    "Apery zeta(3)": lambda m: sum(C(m, k)**2 * C(m + k, k)**2 for k in range(m + 1)),
    "Domb": lambda m: sum(C(m, k)**2 * C(2*k, k) * C(2*m - 2*k, m - k) for k in range(m + 1)),
    "Almkvist-Zudilin": lambda m: sum((-1)**k * 3**(m - 3*k) * C(m, 3*k) * C(m + k, m) * fac(3*k) // fac(k)**3
                                      for k in range(m // 3 + 1)),
    "Cooper s7": lambda m: sum(C(m, k)**2 * C(m + k, k) * C(2*k, m) for k in range(m + 1)),
    "Cooper s10": lambda m: sum(C(m, k)**4 for k in range(m + 1)),
    "Cooper s18": lambda m: sum((-1)**k * C(m, k) * C(2*k, k) * C(2*m - 2*k, m - k) * (C(2*k, m) + C(2*m - 2*k, m))
                                for k in range(m + 1)),
    "binom(2n,n)^3": lambda m: C(2*m, m)**3,
    "franel-sq (Sym^2 Zagier A?)": lambda m: sum(C(m, k)**3 for k in range(m + 1)),
}
for name, s in seqs.items():
    w = [s(m) for m in range(41)]
    g = guess3(w, 30)
    if g is None:
        print(f"{name}: no three-term recurrence of degree <= 3"); continue
    R1, R2 = g
    if sp.Poly(R2, n).eval(0) != 0:
        print(f"{name}: R2 = {R2} not divisible by n"); continue
    y0, q, K = cyk.yukawa(cyk.hadamard_I(R1, R2), DM)
    nd = cyk.instantons(K, DM)
    bad = [d for d in range(1, DM + 1) if nd[d].denominator != 1]
    from sympy import factorint as _fi
    dp = sorted({q for d in bad for q in _fi(nd[d].denominator)})
    print(f"{name}: denominator primes {dp}; R1={R1}, R2={R2}\n   y0 int {all(v.denominator == 1 for v in y0)}, "
          f"q int {all(v.denominator == 1 for v in q)}, K int {all(v.denominator == 1 for v in K)}, "
          f"n_d non-integral at {bad[:6]}, n1..3 = {[str(v) for v in nd[1:4]]}")
