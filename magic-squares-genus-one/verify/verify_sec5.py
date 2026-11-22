"""Claude's independent check of CENTRE_SEXTICS.md section 5 (candidate 85 algebra). SymPy, exact."""
import sympy as S

w, f, g, t, c = S.symbols("w f g t c", nonzero=True)
F, G, T, a = S.symbols("F G T a")
h = lambda p: p**2 + p**-2
psi1, psi2, psi3 = w, w / f, w / g
psi4 = c * psi2 * psi3 / psi1                       # psi1 psi4 = c psi2 psi3
rel1 = h(psi3) - h(psi1) - h(psi2)                  # h3 = h1 + h2
rel2 = h(psi4) - h(psi1) + h(psi2)                  # h4 = h1 - h2
# t = psi1 psi4 = c w^2/(f g)  =>  w^2 = t f g / c
sub = {w: S.sqrt(t * f * g / c)}
e1 = S.factor(S.together(rel1.subs(sub)))
e2 = S.factor(S.together(rel2.subs(sub)))
# (11): T(FG+G-F)+a(1+F-G)=0, T(FG-G-a)+a(1-F)-FG=0 with F=f^2, G=g^2, T=t^2, a=c^2
c11a = T * (F * G + G - F) + a * (1 + F - G)
c11b = T * (F * G - G - a) + a * (1 - F) - F * G
back = {F: f**2, G: g**2, T: t**2, a: c**2}
for e, ref in ((e1, c11a), (e2, c11b)):
    q = S.cancel(S.numer(S.together(e)) / ref.subs(back))
    assert S.factor(q) in (1, -1), q
    print("ratio to (11):", S.factor(q))
# (12) elimination of T
res = S.factor(S.resultant(c11a, c11b, T))
A = -F**2 + (a - 1) * F - a
B = (1 - 2 * a) * F**2 - a**2 + 2 * a
C = a * F**2 + (a**2 - a) * F + a**2
ratio = S.factor(S.cancel(res / (A * G**2 + B * G + C)))
assert ratio == 1, ratio
print("resultant / (A G^2 + B G + C):", ratio)
D = S.expand(B**2 - 4 * A * C)
assert S.expand(D - ((4*a**2+1)*F**4 + 6*a**2*F**2 + a**4 + 4*a**2)) == 0
print("D == (13): True")
b, Y = S.symbols("b Y")
dy = S.factor(S.discriminant((4*b+1)*Y**2 + 6*b*Y + b**2 + 4*b, Y))
assert S.expand(dy + 16*b*(b+1)**2) == 0, dy
print("disc_Y:", dy)
assert S.expand(S.resultant(A, C, F) - 4*a**3*(a-1)**2) == 0
assert S.expand(S.discriminant(A, F) - (a**2-6*a+1)) == 0
assert S.expand(S.discriminant(C, F) - a**2*(a**2-6*a+1)) == 0
print("res_F(A,C), disc A, disc C: as stated")
# a = 1
q = S.symbols("q")
pa1 = S.factor((-B / A + 2 * q).subs(a, 1))
print("a=1  -B/A+2q:", pa1, " C/A:", S.factor((C / A).subs(a, 1)))
# a = 3 +- 2 sqrt2
for sg in (1, -1):
    av = 3 + sg * 2 * S.sqrt(2)
    r = (av - 1) / 2
    assert S.simplify(r**2 - av) == 0
    assert S.expand(A.subs(a, av) + (F - r)**2) == 0 and S.expand(C.subs(a, av) - av * (F + r)**2) == 0
    for sq in (1, -1):
        qv = sq * S.I * r * (F + r) / (F - r)
        assert S.simplify(qv**2 - (C / A).subs(a, av)) == 0
        expr = S.factor(S.together((-B / A).subs(a, av) + 2 * qv), extension=[S.sqrt(2), S.I])
        num = S.numer(S.together(expr)); den = S.denom(S.together(expr))
        cf = S.Poly(S.expand(num), F).all_coeffs()
        assert len(cf) == 3 and cf[1] == 0 and S.simplify(cf[0]) != 0 and S.simplify(cf[2]) != 0, cf
        assert S.simplify(S.im(cf[0])) != 0 and S.simplify(S.im(cf[2])) != 0
        print(f"a=3{'+' if sg>0 else '-'}2rt2 q sign {sq}: numerator in F:", cf,
              " den:", S.factor(den, extension=[S.sqrt(2), S.I]))
# a = i: verify (16)
s3 = S.sqrt(3)
rr, ss = (s3 - 1) / 2, (s3 + 1) / 2
k = (1 - S.I * (2 + s3)) / 2
ell = 2 * S.I / (1 + S.I * (2 + s3))
Gv = k * (F + rr * (1 - S.I)) / (F + ss * (1 - S.I))
Tv = ell * (F + ss * (1 + S.I)) / (F + rr * (1 + S.I))
chk1 = S.simplify(S.expand(S.numer(S.together(c11a.subs({a: S.I, G: Gv, T: Tv})))))
chk2 = S.simplify(S.expand(S.numer(S.together(c11b.subs({a: S.I, G: Gv, T: Tv})))))
assert chk1 == 0 and chk2 == 0
print("a=i (16) satisfies (11): True")
print("other root G' (product C/A / G):", S.simplify((C / A).subs(a, S.I) / Gv))
# Special values of b = a^2 in the squareness of Delta in C(f), F = f^2 (the claim "Delta is a square exactly when
# a = +-i"): generically Delta = (4b+1)(f^4 - y1)(f^4 - y2) with y1 != y2, both nonzero, so not a square. The
# degenerate cases are disc_Y = 0 (b = 0 is excluded since a = c^2 != 0; b = -1), leading coefficient 0 (b = -1/4)
# and a zero root y = 0 (b^2 + 4b = 0, so b = -4).
fv = S.symbols("fv")
def is_square_poly(p):
    _, fac = S.sqf_list(S.Poly(S.expand(p), fv))
    return all(mult % 2 == 0 for _, mult in fac)
Dn = lambda bv: (4*bv + 1)*fv**8 + 6*bv*fv**4 + bv**2 + 4*bv
for bv, want in ((S.Rational(-1, 4), False), (-4, False), (-1, True), (2, False), (S.Rational(1, 3), False)):
    got = is_square_poly(Dn(bv))
    assert got == want, (bv, got)
    print(f"b = {bv}: Delta square in C(f): {got}")
assert S.expand(Dn(-1) + 3*(fv**4 + 1)**2) == 0
print("b = -1 (a = +-i): Delta = -3 (F^2 + 1)^2: True")
