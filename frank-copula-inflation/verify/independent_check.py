"""Independent verification; no imports from explore/."""
from fractions import Fraction as F
from itertools import combinations_with_replacement
import mpmath as mp
import sympy as sp

mp.mp.dps = 90
mp.iv.dps = 70
iv = mp.iv

def vi(x):
    x = F(x)
    return iv.mpf(x.numerator) / x.denominator

def hullzero(upper):
    return iv.mpf([0, upper.b])

def frank_i(u, v, t):
    u, v, t = vi(u), vi(v), vi(t)
    return -iv.ln(1 + (iv.exp(-t*u)-1)*(iv.exp(-t*v)-1)/(iv.exp(-t)-1))/t

def variance(a):
    return sum((min(u,v)-u*v for u in a for v in a), F(0))

def show(label, x, digits=18):
    # Outward decimal rounding, rather than formatting endpoints to nearest.
    scale = mp.mpf(10)**digits
    lo = mp.floor(mp.mp.make_mpf(x._mpi_[0])*scale)
    hi = mp.ceil(mp.mp.make_mpf(x._mpi_[1])*scale)
    def fmt(n):
        n = int(n)
        return ('-' if n < 0 else '') + str(abs(n)//10**digits) + '.' + str(abs(n)%10**digits).zfill(digits)
    print(label, '['+fmt(lo)+', '+fmt(hi)+']')

a = list(map(F, ['27/250','193/1000','13/50','8/25','187/500','17/40','19/40',
                  '21/40','23/40','313/500','17/25','37/50','807/1000','223/250']))
assert len(a) == 14 and all(0 < x < y < 1 for x,y in zip(a,a[1:]))
var = variance(a)
cov = sum((frank_i(u,v,10)-vi(u*v) for u in a for v in a), iv.mpf(0))
rho_xy = cov/vi(var)
print('CLAIM 1: 14 cutpoints; variance =', var)
show('covariance', cov)
show('ordinal correlation', rho_xy)

# J1 = pi^2/6 - A; J2 = 2*zeta(3) - B.
# The integral test bounds zeta(3)-sum(n^-3,n=1..N).
N, K, t = 10000, 10, vi(10)
z3partial = sum((iv.mpf(1)/n**3 for n in range(1,N+1)), iv.mpf(0))
z3 = z3partial + iv.mpf([vi(F(1,2*(N+1)**2)).a, vi(F(1,2*N**2)).b])
A = sum((iv.exp(-n*t)*(1+n*t)/n**2 for n in range(1,K+1)), iv.mpf(0))
B = sum((iv.exp(-n*t)*(2+2*n*t+(n*t)**2)/n**3 for n in range(1,K+1)), iv.mpf(0))
geotail = iv.exp(-(K+1)*t)/(1-iv.exp(-t))
A += hullzero((1+t)*geotail)
B += hullzero((2+2*t+t*t)*geotail)
J1, J2 = iv.pi**2/6-A, 2*z3-B
rho_s = 1-12*J1/t**2+24*J2/t**3
show('Spearman rho', rho_s)
show('strict gap', rho_xy-rho_s)
assert (rho_xy-rho_s).a > 0
print('rho certification: iv.dps=70; zeta3 N=10000; exponential tails K=10')
# The published claims of Proposition 5.1 (independent recheck at lower precision).
PAPER_CUTS = "27/250, 193/1000, 13/50, 8/25, 187/500, 17/40, 19/40, 21/40, 23/40, 313/500, 17/25, 37/50, 807/1000, 223/250"
assert a == [F(c) for c in PAPER_CUTS.split(', ')], 'cut-points differ from the paper'
# The bounds below are coarser than the paper's enclosures (this program works at lower precision); they confirm
# the printed decimals of corr, rho_S and the gap, not the 25-digit enclosures, which certify_arb.py checks.
assert var == F(11727, 500), 'variance'
def inside(x, lo, hi): return vi(F(lo)).a <= x.a and x.b <= vi(F(hi)).b
assert inside(rho_xy, '0.86038678931433', '0.86038678931434'), 'corr(X,Y) differs from the paper'
assert inside(rho_s, '0.8602336388081', '0.8602336388083'), 'rho_S differs from the paper'
assert inside(rho_xy - rho_s, '0.0001531505060', '0.0001531505062'), 'gap differs from the paper'
print('published values of Proposition 5.1 confirmed')

# Independent score-cell reconstruction, including boundary cutpoints and ties.
def c_mp(u,v,t):
    u,v = mp.mpf(u.numerator)/u.denominator, mp.mpf(v.numerator)/v.denominator
    if not u or not v: return mp.mpf(0)
    if u == 1: return v
    if v == 1: return u
    if t == 0: return u*v
    if t == mp.inf: return min(u,v)
    return -mp.log1p(mp.expm1(-t*u)*mp.expm1(-t*v)/mp.expm1(-t))/t

def rho_mp(t):
    if t == 0: return mp.mpf(0)
    if t == mp.inf: return mp.mpf(1)
    j1 = mp.quad(lambda x: x/mp.expm1(x) if x else 1, [0,t])
    j2 = mp.quad(lambda x: x*x/mp.expm1(x) if x else 0, [0,t])
    return 1-12*j1/t**2+24*j2/t**3

grid = list(map(F,['0','1/4','1/2','3/4','1']))
cuts = [q for n in range(4) for q in combinations_with_replacement(grid,n)]
valid = [q for q in cuts if variance(q)>0]
print('GRID: multisets of 0..3 cutpoints from {0,1/4,1/2,3/4,1};',len(cuts),'total;',len(valid),'nonconstant')
for t in [mp.mpf(0),mp.mpf('0.001'),mp.mpf(1),mp.mpf(10),mp.mpf(100),mp.inf]:
    tab = {(u,v):c_mp(u,v,t) for u in grid for v in grid}
    maxerr = mp.mpf(0)
    vals = []
    for aa in valid:
        for bb in valid:
            cov1 = sum((tab[u,v]-mp.mpf((u*v).numerator)/(u*v).denominator for u in aa for v in bb),mp.mpf(0))
            av,bv = [F(0),*aa,F(1)],[F(0),*bb,F(1)]
            ex,ey = 1+sum(1-u for u in aa),1+sum(1-v for v in bb)
            cov2 = mp.mpf(0)
            for i,(u0,u1) in enumerate(zip(av,av[1:]),1):
                for j,(v0,v1) in enumerate(zip(bv,bv[1:]),1):
                    p = tab[u1,v1]-tab[u0,v1]-tab[u1,v0]+tab[u0,v0]
                    cov2 += i*j*p
            cov2 -= mp.mpf((ex*ey).numerator)/(ex*ey).denominator
            maxerr=max(maxerr,abs(cov1-cov2))
            va,vb=variance(aa),variance(bb)
            vals.append(cov1/mp.sqrt(mp.mpf(va.numerator)/va.denominator*mp.mpf(vb.numerator)/vb.denominator))
    rs=rho_mp(t)
    violations=sum(x>rs+mp.mpf('1e-65') for x in vals)
    assert maxerr<mp.mpf('1e-65')
    print('t='+str(t)+': cases='+str(len(vals))+'; formula errors <1e-65; violations='+str(violations)+'; max corr='+mp.nstr(max(vals),15)+'; rho='+mp.nstr(rs,15))

# A separate exact-arithmetic check of all moment formulas for checkerboard copulas.
# 2x2 doubly stochastic cell masses: ((k,4-k),(4-k,k))/8, k=0..4.
# Cuts are grid boundaries, so all moments are rational.
exact = 0
for k in range(5):
    masses=[[F(k,8),F(4-k,8)],[F(4-k,8),F(k,8)]]
    def overlap(u,i): return max(F(0),min(u-F(i,2),F(1,2)))*2
    def cc(u,v): return sum(masses[i][j]*overlap(u,i)*overlap(v,j) for i in range(2) for j in range(2))
    for aa in valid:
        for bb in valid:
            cov1=sum((cc(u,v)-u*v for u in aa for v in bb),F(0))
            av,bv=[F(0),*aa,F(1)],[F(0),*bb,F(1)]
            ex,ey=1+sum(1-u for u in aa),1+sum(1-v for v in bb)
            e2=sum((i*j*(cc(u1,v1)-cc(u0,v1)-cc(u1,v0)+cc(u0,v0))
                    for i,(u0,u1) in enumerate(zip(av,av[1:]),1)
                    for j,(v0,v1) in enumerate(zip(bv,bv[1:]),1)),F(0))
            assert cov1==e2-ex*ey
            # Diagonal copula checks the variance formula using identical score cells.
            e_sq=sum((i*i*(u1-u0) for i,(u0,u1) in enumerate(zip(av,av[1:]),1)),F(0))
            assert variance(aa)==e_sq-ex*ex
            exact+=1
print('Exact rational checkerboard moment tests:',exact,'passed')

# Smooth test family c=1+eta*(2u-1)*(2v-1)+theta*(6u^2-6u+1)*(2v-1).
# |eta|+|theta|<=1 guarantees nonnegative density, including its boundary.
u,e,eta,theta=sp.symbols('u e eta theta',real=True)
p=6*u*u-6*u+1
h=theta*p/6
assert sp.integrate(h,(u,0,1))==0
assert sp.integrate(u*h,(u,0,1))==0
rho=(eta/sp.Integer(3)+e*theta**2/15)/sp.sqrt(1+e**2*theta**2/15)
deriv=sp.simplify(sp.diff(rho,e).subs(e,0))
assert deriv==theta**2/15
print('LEMMA exact family: rho(0)=eta/3; derivative='+str(deriv))

def poly_c(u,v,et,th):
    return u*v+et*(u*u-u)*(v*v-v)+th*(2*u**3-3*u*u+u)*(v*v-v)

def round_cuts(th,M):
    # eps=1/2, f(u)=u+theta*p(u)/12, derivative >=1-|theta|/2.
    f=lambda x:x+th*(6*x*x-6*x+1)/12
    lo,hi=f(mp.mpf(0)),f(mp.mpf(1))
    out=[]
    for k in range(int(mp.floor(M*lo))+1,int(mp.ceil(M*hi))):
        target=mp.mpf(k)/M
        left,right=mp.mpf(0),mp.mpf(1)
        for _ in range(260):
            mid=(left+right)/2
            if f(mid)<target:left=mid
            else:right=mid
        out.append((left+right)/2)
    return out

def var_mp(aa):return sum((min(x,y)-x*y for x in aa for y in aa),mp.mpf(0))
for et,th in [('-.5','-.5'),('-.5','.5'),('0','-1'),('0','1'),('.5','-.5'),('.5','.5')]:
    et,th=mp.mpf(et),mp.mpf(th)
    results=[]
    for M in [4,16,64]:
        aa=round_cuts(th,M)
        bb=[mp.mpf(k)/M for k in range(1,M)]
        cv=sum((poly_c(x,y,et,th)-x*y for x in aa for y in bb),mp.mpf(0))
        results.append(cv/mp.sqrt(var_mp(aa)*var_mp(bb))-et/3)
    assert results[-1]>0
    print('eta='+str(et)+', theta='+str(th)+': step gains at M=4,16,64 = '+', '.join(mp.nstr(x,12) for x in results))
print('Affine boundary theta=0: derivative=0; eta=0 is independence, all nonconstant transformed correlations=0.')
