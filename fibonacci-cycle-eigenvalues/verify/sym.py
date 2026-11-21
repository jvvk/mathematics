"""Lemma 3.2 identities, checked symbolically; exits nonzero on failure."""
import sympy as sp
l,a,b=sp.symbols('lambda a b',positive=True)
E=lambda w: sp.Matrix([[1,1/w],[0,1]]); S=sp.Matrix([[1,0],[-l,1]])
MA=E(a)*S; MB=E(b)*S          # letter A has weight a, letter B weight b
z=lambda e: sp.simplify(e)==0
assert z((MA*MB*MA.inv()*MB.inv()).trace()-2 - l**2*(a-b)**2/(a**2*b**2))
assert z(MA.trace()-(2-l/a)) and z(MB.trace()-(2-l/b))
assert z((MA*MB.inv()).trace()-2)                                   # x_{-1}
x2=(MB*MA).trace()                                                  # s_2 = AB
assert z(x2-(l**2-2*(a+b)*l+2*a*b)/(a*b)) and z(x2.subs(l,2*a)+2)
print("ASSERTED Lemma 3.2 identities")
