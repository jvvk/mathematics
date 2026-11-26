import sys as _sys
if not __debug__:
    _sys.exit("refusing to run under python -O: the checks are assertions")
import sympy as sp
t, u, z, q, U = sp.symbols('t u z q U')
w = 1 - u
D = sp.expand((w + t*u**2*(1 + q))**2 - 4*w*t*u**2*(z*w + q))
E1, E2 = D.subs(u, U), sp.diff(D, u).subs(u, U)
sol = sp.solve([E1, E2], [t, q], dict=True)
for s in sol:
    print({k: sp.factor(v) for k, v in s.items()})
# the solution, with U = 1 + p, is the parametrisation (2) of the note
p = sp.symbols('p')
tP = p*(1-p)**2*(1+p*z)/((1+p)**2*(1-p+2*p*z)**2)
qP = z*p*((1-p)**2 - 4*z*p**2)/((1-p)**2*(1+p*z))
assert len(sol) == 1
assert sp.cancel(sol[0][t].subs(U, 1+p) - tP) == 0 and sp.cancel(sol[0][q].subs(U, 1+p) - qP) == 0
print("double-root system solved by the parametrisation (2): checked")
