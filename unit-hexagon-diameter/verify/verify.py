"""Independent exact controls and critical algebra checks for RESEARCH.md."""
import json,sys
from pathlib import Path
import sympy as sp
import z3
from algebraic_search import model

ROOT=Path(__file__).resolve().parent
out={}

def sign(x):
    q=sp.sign(sp.simplify(x))
    if q not in [-1,0,1]:raise AssertionError(f'Undecided exact sign: {x} -> {q}')
    return int(q)

def orient(a,b,c):return sp.simplify((b[0]-a[0])*(c[1]-a[1])-(b[1]-a[1])*(c[0]-a[0]))

def on(a,b,c):
    return all(sign(c[k]-min(a[k],b[k]))>=0 and sign(max(a[k],b[k])-c[k])>=0 for k in [0,1])

def hit(a,b,c,d):
    u,v,w,t=[sign(q) for q in [orient(a,b,c),orient(a,b,d),orient(c,d,a),orient(c,d,b)]]
    return (u==0 and on(a,b,c)) or (v==0 and on(a,b,d)) or (w==0 and on(c,d,a)) or (t==0 and on(c,d,b)) or (u*v<0 and w*t<0)

def audit(p):
    n=len(p);p=[tuple(map(sp.sympify,q)) for q in p]
    unit=all(sp.simplify(sum((p[i][k]-p[(i+1)%n][k])**2 for k in [0,1])-1)==0 for i in range(n))
    contained=all(sign(v)>=0 and sign(1-v)>=0 for q in p for v in q)
    distinct=len(set(p))==n
    crossings=[]
    for i in range(n):
        for j in range(i+1,n):
            if j==i+1 or (i,j)==(0,n-1):continue
            if hit(p[i],p[(i+1)%n],p[j],p[(j+1)%n]):crossings.append([i,j])
    area=sp.simplify(sum(p[i][0]*p[(i+1)%n][1]-p[i][1]*p[(i+1)%n][0] for i in range(n))/2)
    return dict(n=n,unit=unit,contained=contained,distinct=distinct,crossing_edges=crossings,simple=distinct and not crossings and sign(area)!=0)

def odd(k):
    h=1-sp.sqrt(1-sp.Rational(1,4*(k-1)**2));p=[(0,0),(1,0)]
    for j in range(k):
        p.append((1-sp.Rational(j,k-1),1))
        if j<k-1:p.append((1-sp.Rational(2*j+1,2*(k-1)),h))
    return p

out['odd_controls']=[]
for k in [2,3,4,5]:
    r=audit(odd(k));assert r['unit'] and r['contained'] and r['simple'];out['odd_controls'].append(r)
out['square']=audit([(0,0),(1,0),(1,1),(0,1)])
assert all(out['square'][q] for q in ['unit','contained','simple'])
x=json.loads((ROOT/'crossed-exact-hexagon.json').read_text());m=x['denominator'];hex_vertices=[tuple(sp.Rational(v,m) for v in q) for q in x['vertices']]
out['crossed_hexagon']=audit(hex_vertices)
assert out['crossed_hexagon']['unit'] and out['crossed_hexagon']['contained'] and not out['crossed_hexagon']['simple']
out['retraced_hexagon']=audit([(0,0),(1,0),(1,1),(0,1),(sp.Rational(3,5),sp.Rational(1,5)),(0,1)])
assert not out['retraced_hexagon']['distinct'] and not out['retraced_hexagon']['simple']
# A clean exact counterexample to the original proposed disjoint-diagonal exclusion.
a,b=(0,0),(sp.Rational(56,65),sp.Rational(33,65))
c,d=(sp.Rational(9,65),1),(1,sp.Rational(32,65))
assert not hit(a,b,c,d)
assert all(sp.simplify(sum((u[k]-v[k])**2 for k in [0,1]))==1 for u,v in [(a,b),(c,d)])
out['opposite_quadrant_segments']=dict(unit=True,disjoint=True,vertices=[[str(v) for v in p] for p in [a,b,c,d]])

alpha,beta=sp.symbols('alpha beta',real=True)
mix=3-2*sp.cos(alpha)-2*sp.cos(beta)+2*sp.cos(alpha-beta)
fact=4*sp.cos((alpha-beta)/2)*(sp.cos((alpha-beta)/2)-sp.cos((alpha+beta)/2))
assert sp.trigsimp(sp.expand_trig(mix-1-fact))==0
out['mixed_turn_chord_factorization']=True

def solve(s,expected,name):
    s.set(timeout=10000);r=s.check();assert str(r)==expected,(name,str(r),s.reason_unknown() if r==z3.unknown else '')
    out[name]=str(r)

# Exact nonlinear negation of the four-point projection lemma, with no sampled values.
u,v,x,y,l,t=z3.Reals('u v x y l t')
s=z3.SolverFor('QF_NRA');s.add(u*u+v*v==1,z3.Or(u!=1,v!=0),(x-1)**2+y*y==1,x*x+y*y<=2,z3.Or(x!=1,y!=0),l>=0,t>=0,l+t<=1,l*x+t*u==1,l*y+t*v==0)
solve(s,'unsat','four_point_projection_negation')

# Exact real model controls. These certify the encoding accepts valid controls,
# and rejects a genuine crossed equal-edge six-cycle; not a global theorem audit.
s,p=model(4)
for (x,y),(xx,yy) in zip(p,[(0,0),(1,0),(1,1),(0,1)]):s.add(x==xx,y==yy)
solve(s,'sat','square_model_control')
s,p=model(5);rt=z3.Real('positive_sqrt_three');s.add(rt*rt==3,rt>0)
for (x,y),(xx,yy) in zip(p,[(0,0),(1,0),(1,1),(z3.RealVal('1/2'),1-rt/2),(0,1)]):s.add(x==xx,y==yy)
solve(s,'sat','pentagon_model_control')
s,q=model(6)
for (x,y),(xx,yy) in zip(q,hex_vertices):
    s.add(x==z3.RealVal(str(xx)),y==z3.RealVal(str(yy)))
solve(s,'unsat','crossed_hexagon_model_control')

# Check both unit-circle reconstruction formulas algebraically.
dx,dy=sp.symbols('dx dy',real=True);d2=dx*dx+dy*dy;h=sp.sqrt(1/d2-sp.Rational(1,4))
for sg in [-1,1]:
    q=(dx/2-sg*dy*h,dy/2+sg*dx*h)
    assert sp.simplify(sum(v*v for v in q)-1)==0
    assert sp.simplify((q[0]-dx)**2+(q[1]-dy)**2-1)==0
out['circle_intersection_identities']=True
(ROOT/'verification.json').write_text(json.dumps(out,indent=2))
print(json.dumps(out,indent=2))
