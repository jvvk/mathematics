"""Rigorous certificate with Arb (python-flint): corr(X,Y) and rho_S(10) as balls; checks corr > rho_S.
rho_S(t) = 1 - (12/t)(D1 - D2), D_k(t) = (k/t^k) int_0^t s^k/(e^s - 1) ds.
The integral over [0, d] (d = 2^-100) lies in [0, d^k/k] since 0 < s/(e^s-1) <= 1; the rest by acb.integral."""
from fractions import Fraction as Fr
from flint import arb, acb, ctx
ctx.prec = 200
t = 10
cuts = [Fr(27,250), Fr(193,1000), Fr(13,50), Fr(8,25), Fr(187,500), Fr(17,40), Fr(19,40), Fr(21,40), Fr(23,40),
        Fr(313,500), Fr(17,25), Fr(37,50), Fr(807,1000), Fr(223,250)]
q = lambda x: arb(x.numerator)/x.denominator
T = arb(t)
def C(u, v):
    return -(1 + (( -T*q(u)).exp()-1)*((-T*q(v)).exp()-1)/((-T).exp()-1)).log()/T
cov = sum((C(x, y) - q(x*y) for x in cuts for y in cuts), arb(0))
var = q(sum(min(x, y) - x*y for x in cuts for y in cuts))
r = cov/var
d = arb(2)**-100
def I(k):
    main = acb.integral(lambda s, an: s**k/(s.exp()-1), acb(d), acb(t)).real
    return main + arb(0, (d**k/k).upper())          # add [0, d^k/k] as a symmetric widening (conservative)
D = lambda k: arb(k)/T**k*I(k)
rho = 1 - 12/T*(D(1)-D(2))
print("corr  =", r.str(25, radius=True)); print("rho_S =", rho.str(25, radius=True))
gap = r - rho; print("gap   =", gap.str(15, radius=True))
assert gap > 0, "not certified"
# The published claims of Proposition 5.1: any change of theta, cut-points or method must fail here.
# Cut-points exactly as printed in the paper (introduction and Proposition 5.1).
PAPER_CUTS = "27/250, 193/1000, 13/50, 8/25, 187/500, 17/40, 19/40, 21/40, 23/40, 313/500, 17/25, 37/50, 807/1000, 223/250"
assert t == 10 and cuts == [Fr(c) for c in PAPER_CUTS.split(", ")], "cut-points differ from the paper"
assert sum((min(x, y) - x*y for x in cuts for y in cuts), Fr(0)) == Fr(11727, 500), "variance"
paper_corr = arb("0.8603867893143344074910842", "9e-27")
paper_rho = arb("0.8602336388082110151918579", "1.1e-26")
assert paper_corr.contains(r), "corr(X,Y) outside the paper's enclosure"
assert paper_rho.contains(rho), "rho_S outside the paper's enclosure"
assert arb("1.5315050612339e-4", "1e-16").contains(gap), "gap differs from the paper"
print("CERTIFIED (Arb): corr(X,Y) > rho_S(10); paper's enclosures confirmed")
