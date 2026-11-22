"""Exact algebra checks and certificate audit for CENTRE_SEXTICS.md."""
import json
from pathlib import Path
import sympy as S
from centre_sextic import all_forced, rows_of, degree, square_obstruction, forced_value, H

HERE = Path(__file__).resolve().parent
F, G, T, a, b, x = S.symbols('F G T a b x')
q1 = T*(F*G+G-F)+a*(1+F-G)
q2 = T*(F*G-G-a)+a*(1-F)-F*G
A = -F**2+(a-1)*F-a
B = (1-2*a)*F**2-a**2+2*a
C = a*F**2+(a**2-a)*F+a**2
P = A*G**2+B*G+C
assert S.expand(S.resultant(q1,q2,T)-P) == 0
D = S.factor(B**2-4*A*C)
assert S.expand(D-((4*a**2+1)*F**4+6*a**2*F**2+a**4+4*a**2)) == 0
assert S.factor(S.resultant(A,C,F)) == 4*a**3*(a-1)**2
assert S.factor(S.discriminant(A,F)) == a**2-6*a+1
assert S.factor(S.discriminant(C,F)) == a**2*(a**2-6*a+1)
y = S.symbols('y')
assert S.factor(S.discriminant((4*b+1)*y**2+6*b*y+b*(b+4), y)) == -16*b*(b+1)**2
print('monomial resultant, discriminant, and special-parameter classification: verified')

# One embedding; its four field conjugates exhaust a=+-i and sqrt(-3)=+-i*sqrt(3).
i, s = S.I, S.sqrt(3)
r, t = (s-1)/2, (s+1)/2
k = (1-i*(2+s))/2
ell = 2*i/(1+i*(2+s))
G0 = k*(F+r*(1-i))/(F+t*(1-i))
T0 = ell*(F+t*(1+i))/(F+r*(1+i))
GF = (-B+i*s*(F**2+1))/(2*A)
assert S.cancel(GF.subs(a,i)-G0, extension=[i,s]) == 0
assert S.cancel(q1.subs({a:i,G:G0,T:T0}), extension=[i,s]) == 0
assert S.cancel(q2.subs({a:i,G:G0,T:T0}), extension=[i,s]) == 0
constants = [r*(1-i), t*(1-i), t*(1+i), r*(1+i)]
assert all(S.simplify(c) != 0 for c in constants)
assert all(S.simplify(constants[j]-constants[k]) != 0
           for j in range(4) for k in range(j))
polynomials = [S.Poly(x*x+c, x, extension=[i,s]) for c in constants]
assert all(S.gcd(p,p.diff()).degree()==0 for p in polynomials)
assert all(S.gcd(polynomials[j],polynomials[k]).degree()==0
           for j in range(4) for k in range(j))
print('a=+-i: four nonzero, squarefree, pairwise coprime branch quadratics verified')

# Positive control: on y^2=x^3-x, deg(x)=2 and deg(y)=3, and y^4
# really is a rational square. The square obstruction must retain it.
assert square_obstruction((x**3-x)**2) is None
assert square_obstruction(x**3-x) is not None
print('square test: elliptic positive control retained; nonsquare control rejected')

# Audit the arithmetic certificates without Smith decomposition or torsion searches.
source = json.loads((HERE/'m6_distinct_survivors.json').read_text())
report = json.loads((HERE/'m6_centre_sextic_certificates.json').read_text())
assert len(report['exclusions']) == len(source) == 202
assert sorted(z['index'] for z in report['exclusions']) == list(range(202))
counts = {}
for exclusion in report['exclusions']:
    cfg = source[exclusion['index']]['cfg']
    rows = rows_of(cfg)
    why, c = exclusion['reason'], exclusion['certificate']
    counts[why] = counts.get(why,0)+1
    if why == 'forced coincidence':
        full = c['relation_rows']
        assert full[:4] == [list(r) for r in rows]
        # Check every added relation is a justified full fibre of a forced monomial.
        allowed = []
        for (j,k,sign), lst in all_forced(cfg).items():
            dv = [u+sign*v for u,v in zip(rows[j],rows[k])]
            delta = degree(dv)
            for point, multiplicity, value in lst:
                if delta and multiplicity == delta:
                    rel = [max(u,0) for u in dv]
                    rel[point] -= delta
                    allowed.append(rel)
        assert all(r in allowed for r in full[4:])
        j,k = c['points']
        assert j != k
        target = [int(p==j)-int(p==k) for p in range(len(cfg))]
        assert [sum(z*r[p] for z,r in zip(c['coefficients'],full))
                for p in range(len(cfg))] == target
    elif why == 'all-pair RH':
        j,k,sign = c['monomial']
        dv = [u+sign*v for u,v in zip(rows[j],rows[k])]
        delta = degree(dv)
        ram = sum(abs(u)-1 for u in dv if u)
        ram += sum(r-1 for p,r,z in all_forced(cfg)[j,k,sign])
        assert dv == c['divisor'] and delta > 0
        assert ram == c['ramification'] > c['bound'] == 2*delta
    elif why == 'degree-two pencil square obstruction':
        sa,sb,sc = c['signs']; j,k,l = c['A'],c['B'],c['C']
        assert degree(rows[l]) == 3
        vs = []
        for idx,sgn in [(j,sa),(k,sb)]:
            v=[0]*4;v[idx]=sgn;v[l]=-sc;vs.append(v)
        divs = [[sum(v[z]*rows[z][p] for z in range(4))
                 for p in range(len(cfg))] for v in vs]
        pole,p,q = c['pole'],c['fzero'],c['gzero']
        assert len({pole,p,q}) == 3
        assert divs[0] == [2*int(z==p)-2*int(z==pole) for z in range(len(cfg))]
        assert divs[1] == [2*int(z==q)-2*int(z==pole) for z in range(len(cfg))]
        f0,g0 = S.Rational(c['F']),S.Rational(c['G'])
        forced = all_forced(cfg)
        direct_f = forced_value(vs[0],q,forced)
        direct_g = forced_value(vs[1],p,forced)
        assert str(direct_f) == c['values']['F_direct']
        assert str(direct_g) == c['values']['G_direct']
        if direct_f is None:
            t = c['values']['F_recovered_at']
            assert t not in [pole,p,q]
            assert forced_value(vs[1],t,forced) == direct_g == g0
            assert forced_value(vs[0],t,forced)/4 == f0
        else:
            assert direct_f == f0
        if direct_g is None:
            t = c['values']['G_recovered_at']
            assert t not in [pole,p,q]
            assert forced_value(vs[0],t,forced) == direct_f == f0
            assert forced_value(vs[1],t,forced)/4 == g0
        else:
            assert direct_g == g0
        aa,bb,cc = c['coefficients']
        assert all(aa*H[j][z]+bb*H[k][z]+cc*H[l][z]==0 for z in range(2))
        R = S.cancel(-(aa/(f0*x*x)+bb/(g0*(x-1)**2)+cc)
                     /(aa*f0*x*x+bb*g0*(x-1)**2+cc))
        assert S.cancel(R-S.sympify(c['R'])) == 0
        assert square_obstruction(R) == c['odd_factor']
    elif why == 'three affine functions':
        signs=c['signs']; ds=[]
        for j in range(1,4):
            ds.append([signs[j]*rows[j][p]-signs[0]*rows[0][p] for p in range(6)])
        assert ds == c['divisors']
        assert all(sorted(t for t in d if t)==[-2,2] for d in ds)
        assert len({d.index(-2) for d in ds})==1
        assert len({d.index(2) for d in ds})==3
    elif why == 'four-function monomial relation':
        signs=c['signs']; v=[signs[0],-signs[1],-signs[2],signs[3]]
        assert all(sum(v[j]*rows[j][p] for j in range(4))==0 for p in range(6))
        s0,s1,s2,s3 = signs
        vs = [[s0,-s1,0,0],[s0,0,-s2,0],[s0,0,0,s3]]
        assert [[sum(v[j]*rows[j][p] for j in range(4)) for p in range(6)]
                for v in vs] == c['f_g_t_divisors']
        assert all(degree(r)==2 for r in c['f_g_t_divisors'])
    else:
        raise AssertionError(why)
assert counts == report['counts']
print('202 exclusion certificates audited:',counts)
