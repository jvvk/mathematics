"""Symbolic proof that L = Sym^2(D) (up to a left factor).
D: θ²y = p θy + q y with p, q from D = (1-40x+432x^2)θ² - 4x(5θ+1)... rewritten.
Build θ^k(y^2) in the basis (y^2, y θy, (θy)^2) and find the order-3 relation; compare with L."""
import sympy as sp

x, Y, Y1 = sp.symbols("x Y Y1")
# D = θ² − 4x(10θ²+5θ+1) + 48x²(9θ²+9θ+2)  =>  (1-40x+432x²) θ²y = (20x - 432x²) θy + (4x - 96x²) y
lead = 1 - 40*x + 432*x**2
p = (20*x - 432*x**2) / lead
q = (4*x - 96*x**2) / lead


def th(expr):   # θ of an expression in x, Y (=y), Y1 (=θy), using θY = Y1, θY1 = pY1 + qY
    return x*sp.diff(expr, x) + sp.diff(expr, Y)*Y1 + sp.diff(expr, Y1)*(p*Y1 + q*Y)


w = [Y**2]
for _ in range(3):
    w.append(sp.expand(sp.together(th(w[-1]))))
basis = [Y**2, Y*Y1, Y1**2]


def coords(e):
    e = sp.together(e)
    num, den = sp.fraction(e)
    P = sp.Poly(sp.expand(num), Y, Y1)
    return [sp.simplify(P.coeff_monomial(m) / den) for m in basis]


Mx = sp.Matrix([coords(e) for e in w])   # 4 x 3
ns = Mx.T.nullspace()[0]                 # relation c0 w + c1 θw + c2 θ²w + c3 θ³w = 0
ns = sp.simplify(ns / ns[3])
T = sp.symbols("T")
# L in θ-form: θ³ − 4x(2θ+1)(5θ²+5θ+2) + 48x²(θ+1)(3θ+2)(3θ+4), divided by its θ³ coefficient
Lpoly = sp.expand(T**3 - 4*x*(2*T+1)*(5*T**2+5*T+2) + 48*x**2*(T+1)*(3*T+2)*(3*T+4))
Lc = [Lpoly.coeff(T, k) for k in range(4)]
Lc = [sp.simplify(v / Lc[3]) for v in Lc]
ok = all(sp.simplify(ns[k] - Lc[k]) == 0 for k in range(4))
print("Sym^2(D) normalised coefficients equal L's:", ok)
print("PASS prove_symsq" if ok else "FAIL prove_symsq")
assert ok, "Sym^2(D) coefficients differ from L"
