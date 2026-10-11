"""Can a Hadamard transfer lemma  'integral structure on L with alpha1 = x  =>  integral structure on
P = I*L with alpha1 = x'  hold?  L's alpha1 is free (lift t^p fixed). Test which alpha1 survive on P when
only the jets j < J are required integral."""
import sys
from frob_struct import structure, solve_alpha, cyk, frob_P, plog, modp, T
from sympy import legendre_symbol

OPS = {"bogner": [T**3, -4*(2*T+1)*(5*T**2+5*T+2), 48*(T+1)*(3*T+2)*(3*T+4)],
       "apery": [T**3, -(2*T+1)*(17*T**2+17*T+5), (T+1)**3]}
name, p, R, s = sys.argv[1], int(sys.argv[2]), int(sys.argv[3]), int(sys.argv[4])
Lq = OPS[name]
cyk.E = 3
a = cyk.frob(Lq, R)
A = structure([[a[N][j] for j in range(3)] for N in range(R + 1)], p, R, 3)
got, c = solve_alpha(A, p, 3, s)
print(f"L={name} p={p}: alpha1 values surviving mod p^{got}: {len(sorted({x[0] % p**got for x in c}))} (of {p**got})")
cyk.E = 4
a = frob_P(Lq, R)
A = structure([[a[N][j] for j in range(4)] for N in range(R + 1)], p, R, 4)
cp = int(legendre_symbol(2, p)) * 2 ** ((p - 1) // 2)
for J in (2, 3, 4):
    got, c = solve_alpha(A[:J], p, 4, s)
    vals = sorted({x[0] % p**got for x in c})
    print(f"P=I*{name} p={p} jets<{J}: alpha1 mod p^{got}: {vals[:6]}{'...' if len(vals)>6 else ''} "
          f"(#{len(vals)}); predicted {modp(plog(cp,p,s+3)/p,p,got)}")
