"""Exact symbolic checks for the genus-five obstruction's short coefficient table.

These checks support, rather than replace, the proofs in CENTRE_DISTINCT.md.
"""
import sympy as S

x, A, B, z = S.symbols("x A B z")
p, q = A*x**4 + 2*x**2 + B, A*x**4 - 2*x**2 + B
disc = S.factor(S.discriminant(p, x))
res = S.factor(S.resultant(p, q, x))
assert disc == 256*A*B*(A*B - 1)**2
assert res == 256*A**2*B**2
print("quartic discriminant:", disc)
print("plus/minus resultant:", res)

table = [
    ("12", 2+z, 2-z, set()),
    ("34", (2+z)/4, (2-z)/4, {-2, 2}),
    ("13/14/23", 2-z, 5-2*z, {2}),
    ("24", 2+z, 5+2*z, {-2}),
]
for name, product1, product2, expected in table:
    allowed = set()
    for a in (0, 1):
        for b in (0, 1):
            for value in S.solve(product1-a, z):
                if S.simplify(product2.subs(z, value)-b) == 0:
                    allowed.add(value)
    assert allowed == expected
    print(name, "allowed z:", sorted(allowed))

# At AB=1 all four solutions are rational in f, as used in the proof.
Y, f, a = S.symbols("Y f a", nonzero=True)
assert S.expand((Y**2-a**2*f**2)*(Y**2-a**-2*f**-2)
                - (Y**4-(a**2*f**2+a**-2*f**-2)*Y**2+1)) == 0
print("AB=1 rational factorization: verified")
