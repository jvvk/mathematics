"""Remaining links of the proof.
(a) the parametrisation satisfies the quartic factor of the resultant; p = t + O(t^2), q = O(t).
(b) Om(s,m) equals (-1)^(m+1) [x^m] P(s), P(s) = x C_s 3F2[s+1/2,s+1,s+3/2; 1/2,3/2; x^2] - x^2 4^s 3F2[s+1,s+3/2,s+2; 3/2,2; x^2]
    (A336110's defining formula): a finite exact check, s <= 10, r <= 20. The general identity is Lemma 2 of the
    note, proved by hand.
(c) sanity: series of H from the parametrisation equals Sum Om(k,m) y^k z^m for k <= 6, m <= 8."""
import sys as _sys
if not __debug__:
    _sys.exit("refusing to run under python -O: the checks are assertions")
import sympy as sp
p, z, t, q, r, s = sp.symbols('p z t q r s')
tP = p*(1-p)**2*(1+p*z)/((1+p)**2*(1-p+2*p*z)**2)
qP = z*p*((1-p)**2 - 4*z*p**2)/((1-p)**2*(1+p*z))
u = sp.symbols('u'); w = 1 - u
D = sp.expand((w + t*u**2*(1 + q))**2 - 4*w*t*u**2*(z*w + q))
quartic = [f for f, _ in sp.factor_list(sp.resultant(D, sp.diff(D, u), u))[1] if sp.degree(f, q) == 4][0]
assert sp.cancel(quartic.subs({t: tP, q: qP})) == 0
assert sp.series(tP, p, 0, 2).removeO() == p and qP.subs(p, 0) == 0
print("(a) parametrisation solves the quartic; quartic at t=0 is", sp.factor(quartic.subs(t, 0)))

# (b) exact check for s <= 10, r <= 20 (the general identity is Lemma 2 of the note, proved by hand and in Lean)
for s_ in range(1, 11):
    Om = lambda m: sp.Rational(12**s_, sp.factorial(s_+1)*sp.factorial(2*s_+1))*sp.Mul(*[sp.binomial(m+2*L, 3) for L in range(1, s_+1)])
    for rr in range(0, 21):
        a = sp.rf(s_+sp.Rational(1,2), rr)*sp.rf(s_+1, rr)*sp.rf(s_+sp.Rational(3,2), rr)/(sp.rf(sp.Rational(1,2), rr)*sp.rf(sp.Rational(3,2), rr)*sp.factorial(rr))
        b = sp.rf(s_+1, rr)*sp.rf(s_+sp.Rational(3,2), rr)*sp.rf(s_+2, rr)/(sp.rf(sp.Rational(3,2), rr)*sp.rf(2, rr)*sp.factorial(rr))
        assert Om(2*rr+1) == sp.catalan(s_)*a and Om(2*rr+2) == 4**s_*b, (s_, rr)
print("(b) Om(s,2r+1) = C_s a_r and Om(s,2r+2) = 4^s b_r for s <= 10, r <= 20")

# (c) series sanity
y, Z = sp.symbols('y Z')
K, M = 6, 8
pser = sp.Integer(0)
for _ in range(K + 1):  # invert t = tP(p) by fixed point: p = t * p / tP(p)
    pser = sp.series(t*(1+pser)**2*(1-pser+2*pser*z)**2/((1-pser)**2*(1+pser*z)), t, 0, K+1).removeO()
qser = sp.series(qP.subs(p, pser), t, 0, K+1).removeO()
H = sp.series(((z + qser)/(1 - z)).subs(t, y/(1-z)**3), y, 0, K+1).removeO()
for k in range(0, K+1):
    hk = sp.series(H.coeff(y, k), z, 0, M+1).removeO()
    for m in range(1, M+1):
        om = sp.Rational(12**k, sp.factorial(k+1)*sp.factorial(2*k+1))*sp.Mul(*[sp.binomial(m+2*L,3) for L in range(1,k+1)])
        assert hk.coeff(z, m) == om, (k, m, hk.coeff(z, m), om)
print("(c) H series = Om for k <=", K, "m <=", M)
