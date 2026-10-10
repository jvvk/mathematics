"""Finite audits of the hand proof; no sampling estimate is a theorem.
Control and six mutations: timeout 120 nice -n 15 ~/.venvs/main/bin/python run_checks.py.
"""
import os
for key in ['OMP_NUM_THREADS','OPENBLAS_NUM_THREADS','MKL_NUM_THREADS','VECLIB_MAXIMUM_THREADS']:
    os.environ[key]='1'
import argparse,itertools,math
from fractions import Fraction as F
from scipy.integrate import quad
p=argparse.ArgumentParser()
p.add_argument('--mutant',choices=['root_sign','coefficient','cap_dimension','derivative','mixture','ball_density'])
mut=p.parse_args().mutant
checks=0
def require(value,message):
    global checks
    checks+=1
    if not value:raise AssertionError(message)
def close(x,y,message):require(abs(x-y)<2e-10,message+f': {x} versus {y}')
# Exact product certificate and independently integrated middle-vertex cap.
triples=[(F(a),F(b),F(c)) for a in range(1,11) for b in range(1,a+1) for c in range(1,b+1)]
triples.insert(0,(F(5),F(4),F(3)))
for a,b,c in triples:
    h2=b*b+c*c-a*a
    lhs=b*b*c*c-a*a*h2
    rhs=(a*a+(-b*b if mut!='derivative' else b*b))*(a*a-c*c)
    require(lhs==rhs,'product identity')
    if h2>=0:require(lhs>=0,'derivative certificate')
    H2=a*a+c*c-b*b
    primitive=lambda m:H2*m-(m-b)**3/F(3)
    actual=(primitive(a+c)-primitive(a-c))/(8*a*b*c)
    target=(a-b)/(2*a)+c*c/(6*a*b)
    require(actual==target,'middle cap polynomial integral')
# Independently clipped cap integrals: condition on two vectors' dot product.
# The reference evaluates the defining cap probability before radius ordering.
def obtuse_ref(u,v,w):
    lo=abs(u-v);hi=u+v
    h2=u*u+v*v-w*w
    edges=[lo,hi]
    if h2>=0:
        h=math.sqrt(h2)
        edges.extend(x for x in [h-w,w-h,w+h] if lo<x<hi)
    edges=sorted(set(edges))
    def density(m):
        if m==0:return 0.
        threshold=(m*m+2*w*w-u*u-v*v)/(2*w*m)
        if threshold<=-1:q=1.
        elif threshold>=1:q=0.
        elif mut=='cap_dimension':q=math.acos(threshold)/math.pi
        else:q=(1-threshold)/2
        return m*q/(2*u*v)
    return sum(quad(density,l,h,epsabs=2e-12,epsrel=2e-12)[0] for l,h in zip(edges,edges[1:]))
def formula(a,b,c):
    a,b,c=sorted((a,b,c),reverse=True)
    h=math.sqrt(max(0.,b*b+c*c-a*a))
    coefficient=5 if mut=='coefficient' else 6
    sign=1 if mut=='root_sign' else -1
    return b/(2*a)+c*c/(coefficient*a*b)+sign*h**3/(6*a*b*c)
cases=[(1.,1.,c) for c in [.01,.1,.3,.7,1.]]
cases += [(1.,b,c) for b in [.1,.3,.5,.7,.9,.99,1.] for c in [.05,.1,.3,.5,.7,.9,.99] if c<=b]
cases += [(5.,4.,3.),(13.,12.,5.),(2.,1.,1.),(1.,.8,.6)]
for a,b,c in cases:
    h=math.sqrt(max(0.,b*b+c*c-a*a))
    pA=obtuse_ref(b,c,a);pB=obtuse_ref(a,c,b);pC=obtuse_ref(a,b,c)
    close(pA,h**3/(6*a*b*c),'largest cap')
    close(pB,(a-b)/(2*a)+c*c/(6*a*b),'middle cap')
    close(pC,.5-c*c/(3*a*b),'smallest cap')
    direct=1-pA-pB-pC
    close(formula(a,b,c),direct,'total acute formula')
    require(-1e-12<=direct<=.5+1e-12,'radial bound')
    if a==b:close(direct,.5,'equality case')
    else:require(direct<.5-1e-12,'strict inequality case')
# Permutation symmetry is checked independently by the defining cap integrals.
for radii in itertools.permutations((1.,.9,.7)):
    close(formula(*radii),1-sum(obtuse_ref(radii[(i+1)%3],radii[(i+2)%3],radii[i]) for i in range(3)),'permutation symmetry')
# Exact mixture coefficients against explicitly partitioned event probabilities.
for e in [F(0),F(1,100),F(1,10),F(1,4),F(1,2),F(1)]:
    centre=F(1,4) if mut=='mixture' else F(1,2)
    p2=(1-e)**3/F(4)+3*e*(1-e)**2*centre
    p3=(1-e)**3/F(2)+3*e*(1-e)**2*centre
    require(p2==(1-e)**2*(1+5*e)/4,'planar mixture')
    require(p3==(1-e)**2*(1+2*e)/2,'spatial mixture')
    if 0<e<=F(1,4):require(p2>F(1,4),'planar local gain')
    if e>0:require(p3<F(1,2),'spatial strict loss')
require((1-F(1,10))**2*(1+5*F(1,10))/4==F(243,800),'planar mixture at 1/10')
import sympy as _sp
_e=_sp.symbols('e')
require(_sp.diff((1-_e)**2*(1+5*_e)/4,_e).subs(_e,0)==_sp.Rational(3,4),'planar slope at 0')
require(_sp.expand((1-_e)**2*(1+2*_e)/2-(_sp.Rational(1,2)-_sp.Rational(3,2)*_e**2+_e**3))==0,'spatial expansion')
# Direct deterministic geometric sign-pair test for the centre lemma.
def acute(A,B,C):
    points=[A,B,C]
    return all(sum((points[(i+1)%3][j]-points[i][j])*(points[(i+2)%3][j]-points[i][j]) for j in range(len(A)))>0 for i in range(3))
for dim in [2,3]:
    O=(0.,)*dim;U=(1.,)+(0.,)*(dim-1)
    for k in range(31):
        t=2*math.pi*(k+.173)/31
        V=(math.cos(t),math.sin(t)) if dim==2 else (math.cos(t),math.sin(t)*math.cos(.71),math.sin(t)*math.sin(.71))
        require(acute(O,U,V)+acute(O,U,tuple(-x for x in V))==1,'centre sign pairing')
# Exact radial integration plus an independent numerical primitive check.
# Ordered two-radius density integrates to 1.
density=F(12) if mut=='ball_density' else F(18)
require(density/F(18)==1,'ordered radius density normalization')
first=density/F(5*7)
second=F(3,20)*F(2,7)
require(first-second==F(33,70),'ball exact integral')
close(quad(lambda b:3*b*(2*b*b-1)**2.5/5,1/math.sqrt(2),1,epsabs=2e-12)[0],float(second),'ball root integral')
# The rejected planar rectangle shortcut really has zero acute edge triangles.
h=.1;k=math.sqrt(1-h*h);A=(.11,0.)
rectangle=[(h,k),(-h,k),(-h,-k),(h,-k)]
require(sum(acute(A,rectangle[i],rectangle[(i+1)%4]) for i in range(4))==0,'rectangle counterexample')
print(f'PASS: {checks} assertions; {len(triples)} exact radial triples; {len(cases)} cap-integral triples; 6 permutations; centre pairings, mixture and ball checks')
