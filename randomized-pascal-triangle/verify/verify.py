"""Independent exact check: simplex intersections, symbolic polynomials, controls."""
import itertools
import json
import math
from collections import defaultdict
from pathlib import Path
import sympy as s

ROOT=Path(__file__).parent
P,Q=s.symbols('p q')


def independent_planes():
    e=[s.eye(4).row(i) for i in range(4)]
    first=[[e[i]+e[i+1],e[i]-e[i+1],e[i+1]-e[i]] for i in range(3)]
    result=set()
    def add(v):
        v=list(map(int,v));g=math.gcd(*v)
        if not g:return
        v=[z//g for z in v]
        if next(z for z in v if z)<0:v=[-z for z in v]
        result.add(tuple(v))
    for v in e:add(v)
    for i in range(3):add(e[i]-e[i+1])
    for i in range(2):
        add(e[i]-e[i+2]);add(e[i]-2*e[i+1]+e[i+2])
    for i,j in [(0,1),(1,2),(0,2)]:
        for A,B in itertools.product(first[i],first[j]):add(A-B)
    for A,B,C in itertools.product(*first):
        # |A-B|=|B-C| occurs on A=C or A-2B+C=0.
        add(A-C);add(A-2*B+C)
    return sorted(result)


def independent_rays(planes):
    found=set()
    for triple in itertools.combinations(planes,3):
        m=s.Matrix([*triple,[1,1,1,1]])
        if m.det()==0:continue
        x=m.inv()*s.Matrix([0,0,0,1])
        if min(x)<0:continue
        den=s.ilcm(*[z.q for z in x])
        ints=[int(z*den) for z in x]
        g=math.gcd(*ints)
        found.add(tuple(z//g for z in ints))
    return sorted(found)


def polynomial(x,cert):
    weights=list(map(s.Rational,cert['potential']))
    corrections=list(map(s.Rational,cert['corrections']))
    lam=s.Rational(cert['lambda'])
    a,b,c,d=x
    inp=[s.Rational(a+b+c+d,4),s.Rational(abs(a-b)+abs(b-c)+abs(c-d),3),
         s.Rational(abs(a-c)+abs(b-d),2),
         s.Rational(abs(abs(a-b)-abs(b-c))+abs(abs(b-c)-abs(c-d)),2)]
    result=-lam*sum(z*w for z,w in zip(inp,weights))
    result+=corrections[0]*(a+d-b-c)+corrections[1]*(abs(a-b)+abs(c-d)-2*abs(b-c))
    for bits in itertools.product([False,True],repeat=3):
        z=[u+v if h else abs(u-v) for u,v,h in zip([a,b,c],[b,c,d],bits)]
        A,B,C=z
        outputs=[s.Rational(sum(z),3),s.Rational(abs(A-B)+abs(B-C),2),
                 abs(A-C),abs(abs(A-B)-abs(B-C))]
        drift=sum(u*w for u,w in zip(outputs,weights))+corrections[2]*(A+C-2*B)
        k=sum(bits)
        result+=P**k*(1-P)**(3-k)*drift
    return s.Poly(result,P)


def restricted_bernstein(poly,start):
    pp=s.Poly(poly.as_expr().subs(P,start+(1-start)*Q),Q)
    return [sum(pp.nth(j)*s.binomial(k,j)/s.binomial(3,j) for j in range(k+1)) for k in range(4)]


def controls():
    weights=[s.Rational(1),s.Rational(1249,2500),s.Rational(3,100),s.Rational(557,2500)]
    def potential(row):
        x=[0,0,*row,0,0]
        S=sum(row)
        V=sum(abs(a-b) for a,b in zip(x,x[1:]))
        V2=sum(abs(a-b) for a,b in zip(x,x[2:]))
        W=sum(abs(abs(a-b)-abs(b-c)) for a,b,c in zip(x,x[1:],x[2:]))
        return sum(a*b for a,b in zip([S,V,V2,W],weights))
    out={}
    for p in [s.Rational(0),s.Rational(29,125),s.Rational(1,4),s.Rational(1,2),s.Rational(1)]:
        states={(1,):s.Rational(1)}
        values=[]
        old=potential((1,))
        for n in range(1,7):
            nxt=defaultdict(lambda:s.Rational(0))
            for row,prob in states.items():
                for bits in itertools.product([0,1],repeat=len(row)-1):
                    k=sum(bits);w=p**k*(1-p)**(len(bits)-k)
                    if not w:continue
                    interior=[a+b if bit else abs(a-b) for a,b,bit in zip(row,row[1:],bits)]
                    nxt[(1,*interior,1)]+=prob*w
            states=nxt
            mass=sum(prob*sum(row) for row,prob in states.items())
            pot=sum(prob*potential(row) for row,prob in states.items())
            assert sum(states.values())==1
            if p>=s.Rational(29,125):assert pot>=s.Rational(5001,5000)*old
            if p==1:assert mass==2**n
            if p==0:assert mass==2**n.bit_count()
            values.append({'row':n,'states':len(states),'expected_sum':str(mass)})
            old=pot
        out[str(p)]=values
    return out


def main():
    cert=json.loads((ROOT/'certificate.json').read_text())
    planes=independent_planes()
    assert planes==[tuple(z) for z in cert['hyperplanes']]
    rr=independent_rays(planes)
    print('Independent simplex enumeration:',len(planes),'planes,',len(rr),'rays',flush=True)
    report={'planes':len(planes),'rays':len(rr),'certificates':{},'mutations':{}}
    for name,c in cert['certificates'].items():
        assert rr==[tuple(z['ray']) for z in c['rays']]
        for ray,expected in zip(rr,c['rays']):
            bb=restricted_bernstein(polynomial(ray,c),s.Rational(c['p_interval'][0]))
            assert bb==list(map(s.Rational,expected['coefficients']))
            assert min(bb)>=0
        report['certificates'][name]='all 1004 rational coefficients independently matched and nonnegative'
        print(name,'symbolic polynomial check passed',flush=True)
    low=cert['certificates']['low']
    altered=dict(low);altered['lambda']='2'
    report['mutations']['excessive_growth']=any(polynomial(r,altered).eval(s.Rational(29,125))<0 for r in rr)
    report['mutations']['interval_extended_to_zero']=any(polynomial(r,low).eval(0)<0 for r in rr)
    altered=dict(low);altered['potential']=[*low['potential'][:3],'0']
    report['mutations']['variation_term_removed']=any(polynomial(r,altered).eval(s.Rational(29,125))<0 for r in rr)
    assert all(report['mutations'].values())
    print('All three deliberate false certificates rejected',flush=True)
    report['exact_triangle_controls']=controls()
    print('Exact triangle controls through row 6 passed',flush=True)
    report['success']=True
    (ROOT/'validation.json').write_text(json.dumps(report,indent=2)+'\n')


if __name__=='__main__':main()
