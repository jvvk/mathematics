"""Independent nonlinear check of the stated ray, with all periodic seed overlaps.

Uses a direct quadratic apex solver, rather than the supplied bisection simulator.
Constructs affine-law edges exactly and solves the single closure equation anew.
"""
from pathlib import Path
import sys, math, json, random, importlib.util
from fractions import Fraction

root = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(root/'verify'))
from review_simulator import Disk, apex, run

def build(m,n,t):
    c=-t/20
    d0=math.atan2(math.sqrt(3)*m,2*n-m)-2*math.pi/3
    angles=[d0+t/2]*(m-1)+[d0]+[d0+2*math.pi/3-3*t/4]+[d0+2*math.pi/3+t/4]*(n-1)
    def vertices(phi):
        x=y=0.
        points=[]
        for a in angles:
            points.append(Disk(x,y,1+c*y))
            a+=phi
            length=(1+c*y)/(1-c*math.sin(a)/2)
            x+=length*math.cos(a)
            y+=length*math.sin(a)
        return points,x,y
    lo,hi=-.1,.1
    assert vertices(lo)[2]<0<vertices(hi)[2]
    for _ in range(65):
        mid=(lo+hi)/2
        if vertices(mid)[2]>0: hi=mid
        else: lo=mid
    pts,L,y=vertices((lo+hi)/2)
    assert abs(y)<2e-13
    return pts,L,c

def shift(p,k,L): return Disk(p.x+k*L,p.y,p.d)
def free(Q,pts,L,parent_images):
    for j,P in enumerate(pts):
        for k in (-2,-1,0,1,2):
            if (j,k) in parent_images: continue
            if math.hypot(P.x+k*L-Q.x,P.y-Q.y)<(P.d+Q.d)/2-2e-12:
                return False
    return True

results=[]
for m in range(2,9):
    for n in range(2,2*m):
        if not n/2<m<2*n: continue
        for t in (.01,.003,.001):
            pts,L,c=build(m,n,t)
            N=len(pts)
            for i,P in enumerate(pts):
                for j,R in enumerate(pts):
                    for k in (-1,0,1):
                        if i==j and k==0: continue
                        gap=math.hypot(P.x-R.x-k*L,P.y-R.y)-(P.d+R.d)/2
                        assert gap>-3e-12,(m,n,t,i,j,k,gap)
            candidates=[]
            for a in range(N):
                for distance in range(1,N):
                    b=(a+distance)%N
                    sh=int(a+distance>=N)
                    Q=apex(pts[a],shift(pts[b],sh,L),1,c)
                    if Q is not None and free(Q,pts,L,{(a,0),(b,sh)}):
                        candidates.append((Q.y,a,distance-1,Q))
            best=min(candidates,key=lambda x:x[0])
            assert best[1:3]==(m-1,2),(m,n,t,best)
            Z=shift(pts[(m-2)%N],(m-2)//N,L)
            E=shift(pts[(m+2)%N],(m+2)//N,L)
            separation=math.hypot(E.x-Z.x,E.y-Z.y)-(Z.d+E.d)/2-best[3].d
            assert separation>0
            results.append(dict(m=m,n=n,t=t,parent_index=best[1],gap=best[2],ZE_excess=separation))

examples=[]
for eps,c in ((.005,-.0025),(.005,-.00125),(.01,-.005),(.01,-.0025)):
    examples.append(run(.523,eps,c,target=(8,5),max_steps=5000))
expected=[[(362,'T',[2,2]),(367,'T',[3,2]),(1080,'T',[3,3]),(1082,'T',[3,4]),(1084,'T',[3,5])],
          [(724,'T',[2,2]),(731,'T',[3,2]),(2160,'T',[3,3]),(2162,'T',[3,4]),(2163,'P',[3,3])],
          [(182,'T',[2,2]),(185,'T',[3,2]),(542,'T',[3,3]),(543,'T',[3,4]),(544,'T',[3,5])],
          [(362,'T',[2,2]),(369,'T',[3,2]),(1080,'T',[3,3]),(1082,'T',[3,4]),(1083,'P',[3,3])]]
for r,e in zip(examples,expected):
    actual=[(v['step'],v['kind'],v['after']) for v in r['events']]
    assert actual[:len(e)]==e,(actual,e)
assert examples[0]['steps']==2196 and examples[2]['steps']==1101

spec=importlib.util.spec_from_file_location('burst_exact',root/'verify/burst_exact.py')
module=importlib.util.module_from_spec(spec); spec.loader.exec_module(module)
import sympy as sp
rng=random.Random(184)
for _ in range(150):
    coeff=[Fraction(rng.randint(-100,100),rng.randint(1,50)) for _ in range(4)]
    k=module.K(*coeff)
    exact=sum(sp.Rational(v.numerator,v.denominator)*b for v,b in zip(coeff,(1,sp.sqrt(3),sp.sqrt(19),sp.sqrt(57))))
    assert k.sign()==int(sp.sign(exact)),(coeff,k.sign(),sp.sign(exact))
# Pell approximations distinguish values far below the former numerical cutoff.
p,q=2,1
for _ in range(220): p,q=2*p+3*q,p+2*q
tiny=module.K(p,-q)
assert tiny.sign()==1
assert module.K(-p,q).sign()==-1
assert module.K().sign()==0
payload=dict(static_checks=results,examples=examples,exact_sign_random_checks=150,
             exact_sign_pell_digits=len(str(p)),status='passed')
(root/'checks').mkdir(exist_ok=True)
(root/'checks/independent-review.json').write_text(json.dumps(payload,indent=2)+'\n')
print('PASS:',len(results),'independent first-disk checks;',len(examples),'full example histories; 150 field signs and Pell stress test')
