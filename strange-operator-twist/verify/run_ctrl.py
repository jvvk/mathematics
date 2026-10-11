"""Report the set of α1 values (mod p^s) admitting a p-integral Frobenius structure, vs prediction."""
import sys
exec(open('frob_struct.py').read().split('if __name__')[0])
from sympy import legendre_symbol
CTRL = {"apery": [T**3, -(2*T+1)*(17*T**2+17*T+5), (T+1)**3], "domb": [T**3, -2*(2*T+1)*(5*T**2+5*T+2), 64*(T+1)**3], "az": [T**3, -(2*T+1)*(7*T**2+7*T+3), 81*(T+1)**3]}
which, p, R, s = sys.argv[1], int(sys.argv[2]), int(sys.argv[3]), int(sys.argv[4])
Lq = CTRL[sys.argv[5]] if len(sys.argv) > 5 else [T**3, -4*(2*T+1)*(5*T**2+5*T+2), 48*(T+1)*(3*T+2)*(3*T+4)]
if which == "P":
    cyk.E = 4; n = 4; a = frob_P(Lq, R)
else:
    cyk.E = 3; n = 3; a = cyk.frob(Lq, R)
coef = [[a[N][j] for j in range(n)] for N in range(R + 1)]
A = structure(coef, p, R, n)
got, cands = solve_alpha(A, p, n, s)
a1 = sorted({c[0] % p**got for c in cands})
cp = legendre_symbol(2, p) * 2 ** ((p - 1) // 2)
pred = modp(plog(cp, p, s + 3) / p, p, got)
print(f"{which} p={p} R={R}: precision p^{got}, #solutions {len(cands)}, α1 values {a1[:8]}, predicted {pred}, untwisted 0")
