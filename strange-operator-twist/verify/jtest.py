"""Test: is D modular for an index-4 subgroup of PSL2(Z) with signature (0; 2,2,3; one cusp of width 4)?
Then j = C (x-a)^3 / x^4 and j - 1728 = -1728 (x-b)^2 (x^2 - (40/432) x + 1/432) / x^4.
Four coefficient equations, three unknowns (C, a, b): solvability is a genuine test."""
import sympy as sp

x, C, a, b = sp.symbols("x C a b")
lhs = sp.expand(C * (x - a)**3 - 1728 * x**4)
rhs = sp.expand(-1728 * (x - b)**2 * (x**2 - sp.Rational(40, 432) * x + sp.Rational(1, 432)))
eqs = [sp.Eq(lhs.coeff(x, k), rhs.coeff(x, k)) for k in range(4)]
sols = sp.solve(eqs, [C, a, b], dict=True)
print("solutions:", sols)
for s in sols:
    j = s[C] * (x - s[a])**3 / x**4
    print("j(x) =", sp.factor(j))
    # expand j in the mirror coordinate: x = q + ... from modD.py; compare with 1/q_tau + 744
