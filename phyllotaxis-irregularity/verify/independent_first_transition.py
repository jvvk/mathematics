"""Independent check of Lemma 6.1 and the first transition (Theorem B), written by Codex (OpenAI) in the v2
check; it imports none of the other scripts. Exact derivatives of Lemma 6.1, a mesh of possible buried
centres, a grid of local perturbations, and 75 dynamic runs with a direct quadratic apex solver and overlap
checks against every earlier disk, plus three slow-rate runs. Asserts on any failure (nonzero exit).
Run: python3 independent_first_transition.py   (a few minutes; needs SymPy)
"""
import math
from fractions import Fraction as F
from collections import Counter
import sympy as s

u = math.atan(math.sqrt(3)/5)
U = complex(5, math.sqrt(3))/(2*math.sqrt(7))
S = complex(2, -math.sqrt(3))/math.sqrt(7)
V = complex(1, 3*math.sqrt(3))/(2*math.sqrt(7))

def local_algebra():
    rt = s.sqrt
    un = s.Matrix([5, rt(3)])/(2*rt(7))
    sn = s.Matrix([2, -rt(3)])/rt(7)
    vn = s.Matrix([1, 3*rt(3)])/(2*rt(7))
    tangent = s.Matrix([rt(3)/rt(7), 2/rt(7)])
    curve = s.Matrix([1, -vn[0]/vn[1]])
    print('exact derivatives:', s.simplify(un.dot(curve)),
          s.simplify((-sn).dot(curve)), s.simplify(un.dot(tangent)),
          s.simplify(vn.dot(tangent)))
    # Differentiate the two up-triangle contact equations at B=0,d(B)=1.
    # Here E=U, A=-S, triangle apex V, and E_c=U*sin(u)/2.
    matrix=s.Matrix.vstack(vn.T,(-sn).T)
    rhs=s.Matrix([vn[1]/2,(un[1]+vn[1])/2+(-sn).dot(un*un[1]/2)])
    qp=s.simplify(matrix.inv()*rhs)
    fc=s.simplify(un.dot(qp-sn*sn[1]/2)-(-sn[1]+vn[1])/2)
    print('up-triangle clearance derivatives: f_hinge = sqrt(3)/2; f_c =',fc,
          '; switching-hinge derivative =',s.simplify(-fc/(s.sqrt(3)/2)))
    # Rational model: (X,Y) means (X/sqrt(7),sqrt(3)*Y/sqrt(7)).
    Uq, Sq, Vq = (F(5,2), F(1,2)), (F(2), F(-1)), (F(1,2), F(3,2))
    def add(a,b): return tuple(x+y for x,y in zip(a,b))
    for name, vec in [('12',[Sq,Uq,Uq]),('22w1',[Uq,Sq,Vq,Sq]),
                      ('22w2',[Uq,Sq,Sq,Vq]),('22w3',[Uq,Sq,Vq,Sq]),
                      ('22w4',[Uq,Sq,Sq,Vq])]:
        pts=[(F(0),F(0))]
        for v in vec[:-1]: pts.append(add(pts[-1],v))
        ai=0 if name=='12' else (3 if name in ('22w1','22w3') else 1)
        margin=pts[ai][1]-max(p[1] for j,p in enumerate(pts) if j!=ai)
        print(name, 'front Y='+','.join(str(p[1]) for p in pts),
              'A index='+str(ai), 'A height margin in Y='+str(margin))
    parents=[(-Uq[0],-Uq[1]),(-Vq[0],-Vq[1]),Sq]
    count=0; worst=F(0)
    for i in range(-53,54):
        for j in range(-31,-9):
            X,Y=F(i,20),F(j,20)
            if X*X+3*Y*Y>7: continue
            count+=1
            nearest=min(((X-a)**2+3*(Y-b)**2)/7 for a,b in parents)
            assert nearest<1
            worst=max(worst,nearest)
    print('buried-disk cap mesh:',count,'points; max nearest-parent squared distance =',worst)

def apex(p,r,b,c):
    # Local coordinates Q=p+(x,y), contact to p: x^2+y^2=(d(p)+c*y/2)^2.
    # Subtract the two contact equations: dx*x+dy*(1+c^2/4)*y
    # = (dx^2+dy^2-d(p)*c*dy-c^2*dy^2/4)/2.
    z, dp=p; w,dr=r; dx=(w-z).real; dy=(w-z).imag
    if abs(dx)<1e-14: return None
    v=dp # all parents obey the law
    k=dy*(1+c*c/4)/dx
    a=(dx*dx+dy*dy-v*c*dy-c*c*dy*dy/4)/(2*dx)
    aa=1+k*k-c*c/4; bb=-2*a*k-v*c; cc=a*a-v*v
    disc=bb*bb-4*aa*cc
    if disc < -1e-12: return None
    yy=(-bb+math.sqrt(max(0,disc)))/(2*aa)
    zz=z+complex(a-k*yy,yy)
    d=b+c*zz.imag
    if d<=0: return None
    return zz,d

def clearance(q,p): return abs(q[0]-p[0])-(q[1]+p[1])/2

def local_grid():
    import itertools
    n=0; ties=0; failures=0; residual=0
    for ds in itertools.product((-0.002,0,0.002),repeat=6):
        zz=[base+complex(ds[2*i],ds[2*i+1]) for i,base in enumerate((-U,-V,S))]
        for c in (-0.002,-0.0001,0,0.0001,0.002):
            pp=[(z,1+c*z.imag) for z in zz]
            T=apex(pp[0],pp[1],1,c); R=apex(pp[1],pp[2],1,c); P=apex(pp[0],pp[2],1,c)
            assert T and R and P
            n+=1
            for q,ids in ((T,(0,1)),(R,(1,2)),(P,(0,2))):
                residual=max(residual,*(abs(clearance(q,pp[i])) for i in ids))
            te,ra,pb=clearance(T,pp[2]),clearance(R,pp[0]),clearance(P,pp[1])
            if te>=1e-10 and (ra< -1e-10 or R[0].imag>T[0].imag+1e-10): failures+=1
            if ra*pb>1e-18: failures+=1
            if abs(ra)<1e-10: ties+=1
    print('shared-contact grid:',n,'cases;',failures,'failures;',ties,
          'near triple ties; max tangency residual = %.3g'%residual)

def seed(beta,eps,c):
    sa,sb=math.sin(beta+eps/2),math.sin(beta-eps/2)
    sd=-(sa+sb)/(1+c*c*sa*sb/4)
    if abs(sd)>=1: return None
    z=0j; out=[]
    for ang in (math.asin(sd),beta+eps/2,beta-eps/2):
        d=1+c*z.imag
        out.append((z,d))
        z+=d/(1-c*math.sin(ang)/2)*complex(math.cos(ang),math.sin(ang))
    assert abs(z.imag)<1e-12
    return out,z.real

def simulate(beta,eps,c):
    init=seed(beta,eps,c)
    if init is None: return {'invalid':True}
    disks,L=init
    buckets={}
    for k,(z,d) in enumerate(disks): buckets.setdefault(math.floor(z.imag),[]).append(k)
    maxdiam=max(d for z,d in disks)
    # Front cyclic order starts at an arbitrary disk, whose x may have many turns.
    front=[0,1,2]; labels=['D','a','b']; triangles=[]; phase_steps=0; words=Counter()
    max_drift=0; at_start=None; preword=''; phase_start=0; max_h=-math.inf
    max_buried_excess=0.; max_res=0.
    for step in range(1,math.ceil(8/abs(c))+20):
        N=len(front)
        coords=[disks[k][0] for k in front]
        # normalize unwrapping after each arbitrary cyclic rotation
        for k in range(1,N):
            while coords[k].real<=coords[k-1].real: coords[k]+=L
        def edge(k):
            return (coords[(k+1)%N]+(L if k==N-1 else 0))-coords[k]
        bearings={lab:math.atan2(edge(k).imag,edge(k).real) for k,lab in enumerate(labels)}
        if N==4:
            j=labels.index('a'); preword=' '.join(labels[j:]+labels[:j]); words[preword]+=1
            if at_start is None:
                at_start=step; phase_start=step
            targets={'a':u,'D':u-math.pi/3,'b-':u-math.pi/3,'b+':u+math.pi/3}
            max_drift=max(max_drift,max(abs(bearings[x]-targets[x]) for x in labels))
            max_h=max(max_h,math.pi-bearings['a']+bearings['b-'])
            phase_steps+=1
        best=None
        for a in range(N):
            for gap in range(N-1):
                bi=(a+gap+1)%N
                p=(coords[a],disks[front[a]][1]); r=(coords[bi]+(L if bi<=a else 0),disks[front[bi]][1])
                q=apex(p,r,1,c)
                if q is None or (best is not None and q[0].imag>=best[0][0].imag): continue
                if (r[0]-p[0]).real*(q[0]-p[0]).imag-(r[0]-p[0]).imag*(q[0]-p[0]).real<=0: continue
                # Test every historical disk with sufficient vertical proximity, all images via nearest image.
                free=True
                reach=(maxdiam+q[1])/2
                nearby=[oi for bucket in range(math.floor(q[0].imag-reach),math.floor(q[0].imag+reach)+1)
                        for oi in buckets.get(bucket,[])]
                for oi in nearby:
                    z,d=disks[oi]
                    dy=z.imag-q[0].imag; rad=(d+q[1])/2
                    if abs(dy)>rad+1e-10: continue
                    dx=(z.real-q[0].real+L/2)%L-L/2
                    if math.hypot(dx,dy)<rad-1e-10:
                        free=False;break
                if free: best=q,a,gap
        if best is None: return {'failure':'no placement','step':step}
        q,a,gap=best
        for k in (a,(a+gap+1)%N):
            z=coords[k]+(L if k<a else 0)
            max_res=max(max_res,abs(abs(q[0]-z)-(q[1]+disks[front[k]][1])/2))
        removed=[front[(a+t+1)%N] for t in range(gap)]
        if removed: max_buried_excess=max(max_buried_excess,max(disks[k][0].imag-q[0].imag for k in removed))
        if gap>=2: return {'failure':'pentagon','step':step}
        rot=front[a:]+front[:a]; lab=labels[a:]+labels[:a]
        if gap==0:
            origin=lab[0]
            triangles.append((step,origin,preword if N==4 else '12', lab[-1]))
            if len(triangles)==2:
                return dict(triangles=triangles,phase=phase_steps,words=dict(words),
                            drift=max_drift,drift_scaled=max_drift/(abs(eps)+abs(c)),
                            phase_scaled=phase_steps/(abs(eps/c)+1),buried_excess=max_buried_excess,
                            residual=max_res)
            # Rename the first split up b and the untouched up a, independent of initial eps sign.
            if origin not in ('a','b'): return {'failure':'down triangle','step':step}
            lab=['b' if x==origin else ('a' if x in ('a','b') else x) for x in lab]
            front=[rot[0],len(disks)]+rot[1:]
            labels=['b+','b-']+lab[1:]
        else:
            front=[rot[0],len(disks)]+rot[2:]
            labels=[lab[1],lab[0]]+lab[2:]
        buckets.setdefault(math.floor(q[0].imag),[]).append(len(disks))
        maxdiam=max(maxdiam,q[1])
        disks.append((complex(q[0].real%L,q[0].imag),q[1]))
    return {'failure':'timeout'}

def dynamics():
    betas=(u+1e-5,0.36,0.42,0.50,math.pi/6-1e-5)
    epss=(-0.002,-0.0001,0,0.0001,0.002)
    cs=(-0.002,-0.0005,-0.0001)
    n=0; fails=[]; endwords=Counter(); worst_drift=0; worst_steps=0; buried=0; residual=0
    for beta in betas:
        for eps in epss:
            for c in cs:
                r=simulate(beta,eps,c);n+=1
                if 'failure' in r or 'invalid' in r: fails.append((beta,eps,c,r));continue
                endwords[r['triangles'][-1][2]]+=1
                worst_drift=max(worst_drift,r['drift_scaled']);worst_steps=max(worst_steps,r['phase_scaled'])
                buried=max(buried,r['buried_excess']);residual=max(residual,r['residual'])
                assert r['triangles'][1][1]=='a'
    print('dynamics grid:',n,'runs;',len(fails),'failures; second-triangle words:',dict(endwords))
    print('max phase/(|eps/c|+1) = %.6f; max bearing deviation/(|eps|+|c|) = %.6f'%(worst_steps,worst_drift))
    print('max removed-centre excess height = %.3g; max tangency residual = %.3g'%(buried,residual))
    for bad in fails: print('FAIL',bad)
    for c in (-1e-4,-1e-5,-1e-6):
        r=simulate(u+0.001,0.0005,c)
        print('slow-rate beta=u+0.001 eps=0.0005 c=%g:'%c,r)
    for vals in ((0.42,0.002,-0.0005),(0.42,0,-0.0005)):
        r=simulate(*vals)
        print('example',vals,r['triangles'])

if __name__=='__main__':
    local_algebra();local_grid();dynamics()
