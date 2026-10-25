"""Symbolic proof: g(x) = (1-16x)^(-1/4) F(z(x)), z = -6912 x^4/(1-16x)^3, F any solution of the Gauss
equation z(1-z)F'' + (c-(a+b+1)z)F' - ab F = 0 with a=1/12, b=5/12, c=1, is annihilated by
D = θ² − 4x(10θ²+5θ+1) + 48x²(3θ+1)(3θ+2).  Since D has exponents 0,0 at x=0, the holomorphic
solution with value 1 is unique, so f0 = (1-16x)^(-1/4) 2F1(1/12,5/12;1;z)."""
import sympy as sp

x, Z, F0, F1 = sp.symbols("x Z F0 F1")   # F0 = F(z), F1 = F'(z)
a, b, c = sp.Rational(1, 12), sp.Rational(5, 12), 1
z = -6912 * x**4 / (1 - 16*x)**3
pref = (1 - 16*x)**sp.Rational(-1, 4)
F2 = -((c - (a + b + 1)*Z)*F1 - a*b*F0) / (Z*(1 - Z))       # F'' from the Gauss equation


def d_dx(expr):
    """Total x-derivative of an expression in x, F0, F1 with F0' = F1 z', F1' = F2 z'."""
    zp = sp.diff(z, x)
    return sp.diff(expr, x) + sp.diff(expr, F0) * F1 * zp + sp.diff(expr, F1) * F2.subs(Z, z) * zp


def theta(expr):
    return x * d_dx(expr)


g = pref * F0
t1 = theta(g); t2 = theta(t1)
Dg = t2 - 4*x*(10*t2 + 5*t1 + g) + 48*x**2*(9*t2 + 9*t1 + 2*g)
res = sp.simplify(sp.together(Dg.subs(Z, z)))
print("D applied to the pullback simplifies to:", res)
print("PASS prove_pullback" if res == 0 else "FAIL prove_pullback")
assert res == 0, "D does not annihilate the pullback"
