"""Exact check: for n=4F_k the set {lambda : M(lambda)=I} equals the roots of tr M_U, |U|=F_k, all simple."""
import flint, sys
from spec import fibword
Q=flint.fmpq_poly
def mono(word,wt):
    one=Q([1]); zero=Q([]); lam=Q([0,1])
    m=[[one,zero],[zero,one]]
    for c in word:
        iw=flint.fmpq(1,1)/wt[c]
        # E(w) S: [[1-lam/w, 1/w],[-lam, 1]]
        T=[[one-lam*iw, Q([iw])],[-lam, one]]
        m=[[T[0][0]*m[0][0]+T[0][1]*m[1][0], T[0][0]*m[0][1]+T[0][1]*m[1][1]],
           [T[1][0]*m[0][0]+T[1][1]*m[1][0], T[1][0]*m[0][1]+T[1][1]*m[1][1]]]
    return m
def run(kmax,wt):
    F=[0,1]
    while len(F)<kmax+2: F.append(F[-1]+F[-2])
    for k in range(4,kmax+1):
        n=4*F[k]; w=fibword(n); M=mono(w,wt); MU=mono(w[:F[k]],wt)
        g=(M[0][0]-1).gcd(M[0][1]).gcd(M[1][0]).gcd(M[1][1]-1)
        t=MU[0][0]+MU[1][1]
        sqf_t = t.gcd(t.derivative())
        ok = g.degree()==F[k] and sqf_t.degree()==0 and (t % g)==0 or (g.degree()==F[k] and (g % (t.monic() if hasattr(t,'monic') else t))==0)
        print(k,n,"doubles(deg gcd)=",g.degree(),"F_k=",F[k],"tr M_U squarefree:",sqf_t.degree()==0,"gcd | tr:",(t%g)==0, flush=True)
        assert g.degree()==F[k] and sqf_t.degree()==0 and (t%g)==0
if __name__=="__main__":
    kmax=int(sys.argv[1]); a,b=(flint.fmpq(int(x.split('/')[0]),int(x.split('/')[1]) if '/' in x else 1) for x in sys.argv[2:4])
    run(kmax,{"A":a,"B":b})
