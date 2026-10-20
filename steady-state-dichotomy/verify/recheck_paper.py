"""Independent recheck. Shares no code with certify_exact.py or verify_dichotomy.py.
Recomputes every finite claim stated in paper/steady-state-dichotomy.tex from the reaction lists."""
import sympy as sp
x, y, z, lam = sp.symbols("x y z lam")
V = (x, y, z)
R = sp.Rational
ok = []
def check(name, cond): ok.append((name, bool(cond))); print(("PASS " if cond else "FAIL ") + name)

def massaction(net):
    f = [0, 0, 0]
    for src, prod, k in net:
        m = sp.Mul(*[V[i] for i in src])
        for i in range(3): f[i] += (prod.count(i) - src.count(i)) * k * m
    return [sp.expand(e) for e in f]

def Bmat(f):
    # rows i; columns: monomials missing x1, x2, x3 i.e. yz, xz, xy
    mons = [y*z, x*z, x*y]
    return sp.Matrix(3, 3, lambda i, j: sp.Poly(f[i], *V).coeff_monomial(mons[j]))

def rh(f, p):
    J = sp.Matrix(f).jacobian(V).subs(dict(zip(V, p)))
    c = (lam*sp.eye(3) - J).det(); c = sp.Poly(sp.expand(c), lam).all_coeffs()
    b1, b2, b3 = c[1], c[2], c[3]; return b1, b2, b3, b1*b2 - b3, J.det()

# ---- Section 5: seven reactions
net7 = [((0, 1), (), 7), ((0, 2), (1, 2), 1), ((2,), (0,), 1), ((0, 1), (2,), 1), ((1, 2), (0, 1, 2), 1), ((), (1,), 1), ((0,), (0, 2), 3)]
f = massaction(net7)
check("S5 f as printed", f == [sp.expand(e) for e in [-8*x*y - x*z + z + y*z, -8*x*y + x*z + 1, x*y - z + 3*x]])
N7 = sp.Matrix([[p.count(i) - s.count(i) for s, p, _ in net7] for i in range(3)]); check("S5 rank 3", N7.rank() == 3)
check("S5 f2+8f3 identity", sp.expand(f[1] + 8*f[2] - (x*(z + 24) - (8*z - 1))) == 0)
X = (8*z - 1)/(z + 24); Y = (z**2 + 3)/(8*z - 1)
P = z**4 - 96*z**3 + 218*z**2 - 145*z + 24
check("S5 f1 on curve = P/((z+24)(8z-1))", sp.simplify(f[0].subs({x: X, y: Y}) - P/((z + 24)*(8*z - 1))) == 0)
check("S5 P values", [P.subs(z, v) for v in (R(1, 8), R(1, 2), 1, 2, 96)] == [R(37249, 4096), R(-95, 16), 2, -146, 1995192])
check("S5 exactly 4 roots of P in (1/8, oo)", sp.Poly(P, z).count_roots(R(1, 8), sp.oo) == 4)
dJ = sp.Matrix(f).jacobian(V).det()
check("S5 det Df = P'/(z+24) at roots (mod P)", sp.rem(sp.numer(sp.together(dJ.subs({x: X, y: Y}) - sp.diff(P, z)/(z + 24))), P, z) == 0)
B = Bmat(f); check("S5 B as printed", B == sp.Matrix([[1, -1, -8], [0, 1, -8], [0, 0, 1]]))
v = B.inv()*sp.Matrix([1, 1, 1]); check("S5 B^-1 1 = (18,9,1)", list(v) == [18, 9, 1])
w = [1/c for c in v]; Q = [(B*sp.Matrix([1/wi for wi in w]))[i]*w[0]*w[1]*w[2] for i in range(3)]
check("S5 Q_i(w) = 1/162 and gamma = 1/162", all(sp.nsimplify(q) == R(1, 162) for q in Q) and min(Q[i]/w[i] for i in range(3)) == R(1, 162) * 0 + min(Q[i]/w[i] for i in range(3)))
gamma = min(Q[i]/w[i] for i in range(3)); print("   gamma computed =", gamma)
check("S5 escape threshold 2 b*/gamma = 324 (b*=1)", 2*1/gamma == 324)
roots7 = sorted(sp.Poly(P, z).real_roots(), key=lambda r: float(r))
sts = []
for r in roots7:
    rv = sp.N(r, 60); sts.append([sp.N(X.subs(z, rv), 60), sp.N(Y.subs(z, rv), 60), rv])
enc = {0: [(26, 27), (6, 7), (2, 3), (179, 180)], 2: [(9, 10), (13, 14), (1, 2), (125, 126)]}
for k, iv in enc.items():
    vals = rh(f, sts[k])[:4]
    check(f"S5 Routh-Hurwitz enclosures state {k+1}", all(lo < vv < hi for vv, (lo, hi) in zip(vals, iv)))
check("S5 det signs -,+,-,+", [sp.sign(rh(f, s)[4]) for s in sts] == [-1, 1, -1, 1])

# ---- Section 6: eight reactions
net8 = [((0,), (0, 2), 5), ((0,), (1,), 1), ((0, 2), (0, 1, 2), 1), ((0, 1), (1,), 1), ((1, 2), (0,), R(2, 5)), ((2,), (), R(1, 2)), ((), (0, 1), R(1, 2500)), ((1,), (0,), R(1, 100000))]
g = massaction(net8)
check("S6 f as printed", g == [sp.expand(e) for e in [R(1, 2500) - x - x*y + R(2, 5)*y*z + R(1, 100000)*y,
      R(1, 2500) + x + x*z - R(2, 5)*y*z - R(1, 100000)*y, 5*x - z/2 - R(2, 5)*y*z]])
N8 = sp.Matrix([[p.count(i) - s.count(i) for s, p, _ in net8] for i in range(3)]); check("S6 rank 3", N8.rank() == 3)
D = 8000*z**2 - 32000*z - 1; Nn = 10000*z**2 + 10000*z + 40
check("S6 100000 f2 = yD + N after 50x = z(5+4y)", sp.expand((100000*g[1]).subs(x, z*(5 + 4*y)/50) - (y*D + Nn)) == 0)
Yc = -Nn/D; Xc = z*(5 + 4*Yc)/50
E = 40000000000*z**5 - 110031000000*z**4 + 50416250000*z**3 - 782738125*z**2 + 101000*z - 1
check("S6 f2,f3 vanish on curve", sp.simplify(g[1].subs({x: Xc, y: Yc})) == 0 and sp.simplify(g[2].subs({x: Xc, y: Yc})) == 0)
check("S6 f1 on curve = -E/(1250 D^2)", sp.simplify(g[0].subs({x: Xc, y: Yc}) + E/(1250*D**2)) == 0)
check("S6 E table", [E.subs(z, t) for t in (0, R(1, 20000), R(1, 1000), R(1, 10), 1, 3)] ==
      [-1, R(335912964971, 160000000000), R(-316215933, 500000), R(127983471, 4), -20397387126, 2161683409874])
check("S6 exactly 5 positive roots of E, all in (0,3)", sp.Poly(E, z).count_roots(0, 3) == 5 and sp.Poly(E, z).count_roots(0, sp.oo) == 5)
check("S6 D < 0 on (0,3) endpoints/vertex", D.subs(z, 0) < 0 and D.subs(z, 3) < 0)
Mm = sp.Matrix([[sp.diff(g[1], x), sp.diff(g[1], y)], [sp.diff(g[2], x), sp.diff(g[2], y)]]).det()
check("S6 M(z) as printed", sp.expand(Mm - (R(8, 5)*z - R(2, 5)*z**2 + R(1, 20000))) == 0)
dJ8 = sp.Matrix(g).jacobian(V).det()
check("S6 det Df = -M E'/(1250 D^2) at roots (mod E)",
      sp.rem(sp.numer(sp.together(dJ8.subs({x: Xc, y: Yc}) + Mm*sp.diff(E, z)/(1250*D**2))), E, z) == 0)
check("S6 B and det B = -2/5", Bmat(g) == sp.Matrix([[R(2, 5), 0, -1], [R(-2, 5), 1, 0], [R(-2, 5), 0, 0]]) and Bmat(g).det() == R(-2, 5))
roots8 = sorted(sp.Poly(E, z).real_roots(), key=lambda r: float(r))
st8 = [[sp.N(Xc.subs(z, sp.N(r, 80)), 60), sp.N(Yc.subs(z, sp.N(r, 80)), 60), sp.N(r, 60)] for r in roots8]
check("S6 all coordinates positive", all(c > 0 for s in st8 for c in s))
rhs8 = [rh(g, s) for s in st8]
check("S6 det signs -,+,-,+,-", [sp.sign(r[4]) for r in rhs8] == [-1, 1, -1, 1, -1])
stable = [all(q > 0 for q in r[:4]) and r[4] < 0 for r in rhs8]
check("S6 stable = states 1,3,5 (strict RH, 60-digit margins)", stable == [True, False, True, False, True])
print("   min RH quantity at stable states:", min(float(q) for r, s in zip(rhs8, stable) if s for q in r[:4]))
printed = [(2.68e-5, 29.80, 1.08e-5), (9.35e-5, 8.554, 1.19e-4), (0.00210, 0.3966, 0.01595), (0.0814, 0.5690, 0.5591), (0.5964, 2.177, 2.176)]
check("S6 printed coordinates (3 s.f.)", all(abs(float(a) - b) / b < 6e-3 for s, p in zip(st8, printed) for a, b in zip(s, p)))
net7b = net8[:7]; h = massaction(net7b)
check("S6 deleting X2->X1: det B unchanged", Bmat(h).det() == R(-2, 5))
Dh = sp.Matrix(h).jacobian(V).det()
G = sp.groebner(h, x, y, z, order="lex"); e7 = [p for p in G.exprs if p.free_symbols == {z}][0]
pos = 0
for r in sp.Poly(e7, z).real_roots():
    if r <= 0: continue
    sol = sp.solve([p.subs(z, r) for p in G.exprs if p.free_symbols != {z}], [x, y], dict=True)
    for so in sol:
        if all(sp.N(so[s], 40) > 0 for s in (x, y)): pos += 1
check("S6 deleted network has 4 positive states", pos == 4)

# ---- Section 7: strict matrix
C = sp.Matrix([[1, -1, 1, 101, -801, -101, 101], [101, 1, -1, 1, -801, 101, -1], [1, 301, 1, -101, 101, -1, -1]])
mons = [1, x, y, z, x*y, x*z, y*z]
fs = [sp.expand(sum(C[i, k]*mons[k] for k in range(7))) for i in range(3)]
check("S7 C = 100*f7 + strict unit perturbation", all(sp.expand(fs[i] - 100*f[i]) == sp.expand(sum((1 if C[i, k] - 100*sp.Poly(f[i], *V).coeff_monomial(mons[k]) > 0 else -1)*mons[k] for k in range(7))) for i in range(3)))
check("S7 det B = 776596", Bmat(fs).det() == 776596)
G7 = sp.groebner(fs, x, y, z, order="lex"); el = [p for p in G7.exprs if p.free_symbols == {z}][0]
rr = sp.Poly(el, z).real_roots()
check("S7 quintic squarefree, 5 real roots, 1 negative", sp.Poly(el, z).degree() == 5 and len(rr) == 5 and sum(1 for r in rr if r < 0) == 1
      and sp.degree(sp.gcd(el, sp.diff(el, z)), z) == 0)
others = [p for p in G7.exprs if p.free_symbols != {z}]
lifts = []
for r in rr:
    rv = sp.N(r, 80)
    sol = sp.solve([sp.N(p.subs(z, rv), 80) for p in others], [x, y], dict=True)
    for so in sol:
        pt = [so[x], so[y], rv]
        if all(sp.re(c) > 0 and abs(sp.im(c)) < 1e-40 for c in pt): lifts.append([sp.re(c) for c in pt])
lifts.sort(key=lambda q: float(q[2]))
check("S7 four positive lifts", len(lifts) == 4)
rhs7 = [rh(fs, q) for q in lifts]
check("S7 det signs -,+,-,+", [sp.sign(r[4]) for r in rhs7] == [-1, 1, -1, 1])
check("S7 two stable (strict RH)", sum(1 for r in rhs7 if all(q > 0 for q in r[:4]) and r[4] < 0) == 2)
print("\nSUMMARY:", sum(c for _, c in ok), "/", len(ok), "PASS")
import sys
sys.exit(0 if all(c for _, c in ok) else 1)
