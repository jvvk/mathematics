"""Independent finite checks of the simplified proofs and added consequences.
These checks illustrate the proofs; they do not establish them or priority.
"""
from fractions import Fraction as F
from itertools import product
import math
import mpmath as mp
import numpy as np
import sys

MUTANT = sys.argv[2] if len(sys.argv) > 2 and sys.argv[1] == "--mutant" else None


def check_inverse_angles():
    rng = np.random.default_rng(499477)
    worst = 0.0
    for a, b, D in ((.5, 1, 1.5), (1, 1, 2), (3, 1, 4), (.2, 1, 1.2), (.5, 1, 3), (2, 1, 6)):
        for _ in range(100):
            theta = rng.uniform(.05, math.pi-.05, 2)
            def inverse(t, e, n):
                phi = np.arccos((a*np.cos(t[0])-b*np.cos(t[1]))/D)
                return np.array([phi+e*t[0], phi+n*t[1]])
            phi = np.arccos((a*np.cos(theta[0])-b*np.cos(theta[1]))/D)
            g = D*np.sin(phi)
            vals = []
            for e, n in product((-1, 1), repeat=2):
                jac = np.column_stack([(inverse(theta+np.eye(2)[j]*1e-6,e,n)-inverse(theta-np.eye(2)[j]*1e-6,e,n))/2e-6 for j in range(2)])
                expected = 1+e*a*np.sin(theta[0])/g-n*b*np.sin(theta[1])/g
                if MUTANT == "inverse": expected = 1+e*a*np.sin(theta[0])/g+n*b*np.sin(theta[1])/g
                actual = abs(np.linalg.det(jac))
                worst = max(worst, abs(actual-expected))
                assert expected >= -1e-12 and abs(actual-expected) < 1e-7
                vals.append(actual)
            assert abs(sum(vals)-4) < 4e-7
    print(f'Inverse angle determinants: 2,400 finite-difference checks, max error {worst:.2g}')


def check_weights():
    vals = [F(-2),F(-1,3),F(0),F(1,2),F(1),F(5,3)]
    weights = list(product(vals,repeat=2))
    for (a,b),(c,d) in product(weights,repeat=2):
        same_invariants = (abs(a)+abs(b), a*a+b*b)==(abs(c)+abs(d), c*c+d*d)
        if MUTANT == "weights": same_invariants = abs(a)+abs(b)==abs(c)+abs(d)
        assert same_invariants == (sorted([abs(a),abs(b)])==sorted([abs(c),abs(d)]))
    print('Support and second moment: exact for 1,296 comparisons of rational weight pairs')


def check_offaxis():
    vals=[F(1,3),F(1,2),F(1),F(3,2),F(2)]
    count=0
    for a,b in product(vals,repeat=2):
        for D in (a+b,a+b+F(1,4),a+b+1):
            delta=D*D-a*a-b*b
            for h,k in product([F(-2),F(0),F(1,3),F(2),b*D/a], [F(0),F(1,3),F(-3,2)]):
                # Average the independently expanded polynomial W^2+k^2(1-R^2).
                w={ (1,0):-h*a/D, (0,1):b*(1+h/D) }
                r={ (1,0):a/D, (0,1):-b/D }
                def square(poly):
                    out={}
                    for (i,j),u in poly.items():
                        for (l,m),v in poly.items():
                            out[i+l,j+m]=out.get((i+l,j+m),F(0))+u*v
                    return out
                poly=square(w)
                poly[0,0]=k*k
                for mon,c in square(r).items():poly[mon]=poly.get(mon,F(0))-k*k*c
                moments={0:F(1),1:F(0),2:F(1,2)}
                ab=sum(c*moments[i]*moments[j] for (i,j),c in poly.items())
                bc=(b*b+h*h+k*k)/2
                claim=(delta*(k*k-h*h)+2*b*b*D*h)/(2*D*D)
                if MUTANT == "offaxis": claim=(delta*(k*k-h*h)-2*b*b*D*h)/(2*D*D)
                assert ab-bc==claim
                count+=1
    assert (F(3,10)**2)/(2*F(3,2)**2)==F(1,50)
    # Direct line geometry, integrated on a symmetric grid of independent normal-radius angles.
    t=(np.arange(64)+.5)*np.pi/64
    ta,tb=np.meshgrid(t,t,indexing='ij');X,Y=np.cos(ta),np.cos(tb)
    for a,b,D in ((.5,1,1.5),(1,1,2),(2,1,4)):
        phi=np.arccos((a*X-b*Y)/D)
        A=np.stack([-D+a*np.cos(phi+ta),a*np.sin(phi+ta)],axis=-1)
        B=np.stack([b*np.cos(phi+tb),b*np.sin(phi+tb)],axis=-1)
        direction=B-A
        for h,k in ((0,0),(0,.3),(3,.3),(-2,1)):
            direct=(direction[...,0]*(k-A[...,1])-direction[...,1]*(h-A[...,0]))**2/np.sum(direction**2,axis=-1)
            delta=D*D-a*a-b*b
            target=(b*b+h*h+k*k)/2+(delta*(k*k-h*h)+2*b*b*D*h)/(2*D*D)
            assert abs(np.mean(direct)-target)<1e-11,(a,b,D,h,k)
    print(f'Off-axis formula: {count} exact rational cases and 12 direct geometric quadratures')


def hit_integral(r):
    mp.mp.dps=40
    r=mp.mpf(r)
    def clamp(t):return min(mp.mpf(1),max(mp.mpf(-1),t))
    def f(v):
        z=(1+r)*mp.cos(v)
        if MUTANT == "hit": return mp.acos(clamp(z-r))
        return mp.acos(clamp(z-r))-mp.acos(clamp(z+r))
    cuts=[mp.mpf(0),mp.pi/2]
    if r<1:cuts.append(mp.acos((1-r)/(1+r)))
    if r>1:cuts.append(mp.acos((r-1)/(r+1)))
    return 2/mp.pi**2*mp.quad(f,sorted(cuts))


def check_hit_integral():
    angles=(np.arange(1024)+.5)*2*np.pi/1024
    X=np.cos(angles)[:,None];Y=np.cos(angles)[None,:]
    prev=np.zeros((1024,1024),dtype=bool)
    for r in (.25,.5,1,2,4,8):
        event=np.abs(X-(1+r)*Y)<r
        assert np.all(~prev|event)
        p=float(hit_integral(r))
        assert abs(event.mean()-p)<.002,(r,p,event.mean())
        print(f'  r={r:g}: integral {p:.9f}, direct angular grid {event.mean():.9f}')
        prev=event
    special=2/mp.pi**2*mp.quad(lambda v:mp.acos(2*mp.cos(v)-1),[0,mp.pi/2])
    assert abs(hit_integral(1)-special)<mp.mpf('1e-35')
    print('Hit integral: six independent 2D angular grids; nesting and equal-radius specialisation pass')


if __name__=='__main__':
    check_inverse_angles()
    check_weights()
    check_offaxis()
    check_hit_integral()
    print('PASS')
