import sys as _sys
if not __debug__:
    _sys.exit("refusing to run under python -O: the checks are assertions")
import sympy as sp
t, u, z, q = sp.symbols('t u z q')
w = 1 - u
A = w + t*u**2*(1 + q)
D = sp.expand(A**2 - 4*w*t*u**2*(z*w + q))
R = sp.factor(sp.resultant(D, sp.diff(D, u), u))
print(R)
# Step 2 of the note: Res = 256 t^4 (t(1+q)^2 - 4z) R(q,t) with R(q,0) = -zq and R of degree 4 in q.
c, fl = sp.factor_list(R)
quartic = [f for f, e in fl if sp.degree(f, q) == 4]
assert len(quartic) == 1
Rq = quartic[0]
if sp.expand(Rq.subs(t, 0)) == z*q:  # normalise the sign so that R(q,0) = -zq
    Rq = -Rq
assert sp.expand(Rq.subs(t, 0)) == -z*q
assert sp.expand(sp.resultant(D, sp.diff(D, u), u) - 256*t**4*(t*(1+q)**2 - 4*z)*Rq) == 0
print("Res_u(D, D') = 256 t^4 (t(1+q)^2 - 4z) R(q,t) with R(q,0) = -zq: checked")
