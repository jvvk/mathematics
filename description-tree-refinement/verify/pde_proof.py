"""Proof step: the tree series, in the variables y = t(1-z)^3, satisfies the hypergeometric PDE of Om(k,m).

H(y,z) = (z + q)/(1-z), with (t, q) given by the rational parametrisation in p, y = t (1-z)^3.
L = (Ty+1)(2Ty)(2Ty+1) - 2y (Tz+2Ty+2)(Tz+2Ty+1)(Tz+2Ty), Ty = y d/dy, Tz = z d/dz (z-derivative at fixed y).
Om(k,m) = 12^k/((k+1)!(2k+1)!) prod_{L=1..k} C(m+2L,3) satisfies L(Sum Om y^k z^m) = 0 coefficientwise.
"""
import sys as _sys
if not __debug__:
    _sys.exit("refusing to run under python -O: the checks are assertions")
import sympy as sp
p, z = sp.symbols('p z')
t = p*(1-p)**2*(1+p*z)/((1+p)**2*(1-p+2*p*z)**2)
q = z*p*((1-p)**2 - 4*z*p**2)/((1-p)**2*(1+p*z))
y = sp.together(t*(1-z)**3)
H = sp.together((z + q)/(1 - z))
yp, yz = sp.diff(y, p), sp.diff(y, z)

def Ty(f):  # y d/dy at fixed z
    return sp.together(y*sp.diff(f, p)/yp)

def Tz(f):  # z d/dz at fixed y
    return sp.together(z*(sp.diff(f, z) - yz/yp*sp.diff(f, p)))

def A(f, c):  # (Tz + 2Ty + c) f
    return sp.together(Tz(f) + 2*Ty(f) + c*f)

lhs = Ty(H) + H                     # (Ty+1)H
lhs = sp.together(2*Ty(lhs) + lhs)   # (2Ty+1)
lhs = sp.together(2*Ty(lhs))         # (2Ty)
rhs = A(A(A(H, 0), 1), 2)
rhs = sp.together(2*y*rhs)
res = sp.cancel(lhs - rhs)
print("L H =", res)
assert res == 0
print("PDE holds identically")
