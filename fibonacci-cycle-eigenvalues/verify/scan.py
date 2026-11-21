"""Exact scan of all n <= N for double Laplacian eigenvalues of the Fibonacci-weighted n-cycle (Sec. 6).
usage: python scan.py N a b      (a, b positive rationals, e.g. 7/5)
Asserts: at n = 4F_k the double eigenvalues number exactly F_k; every gcd is squarefree (so its degree counts distinct
roots; they are real by Lemma 2.1, L_n being real symmetric). Off n = 4F_k, and only for the five tabulated ratios
b/a (multiplicities depend only on b/a, since scaling both weights scales the spectrum): the doubles are exactly
n in {33, 53, 106}, at lambda = a, for b/a = 2, and none for b/a in {7/15, 3, 5/2, 4}. These are asserted only up to the verified
ranges (n <= 6000 for b/a = 2, n <= 2000 for the others); beyond them, and for other ratios, the exceptional set is
reported, not asserted. Exits nonzero on any failure."""
import flint, sys
from spec import fibword
Q=flint.fmpq_poly; one=Q([1]); zero=Q([]); lam=Q([0,1])
rat=lambda t: flint.fmpq(*map(int,t.split("/")))
N=int(sys.argv[1]); WA=rat(sys.argv[2]); WB=rat(sys.argv[3]); w=fibword(N)
fib=[1,1]
while fib[-1]<N: fib.append(fib[-1]+fib[-2])
fourF={4*F:F for F in fib[3:]}                      # k >= 4: F_k >= 3
r=WB/WA
TAB={flint.fmpq(2):{33,53,106}, flint.fmpq(7,15):set(), flint.fmpq(3):set(), flint.fmpq(5,2):set(), flint.fmpq(4):set()}
expected_sporadic=TAB.get(r)
LIMIT=(6000 if r==2 else 2000) if expected_sporadic is not None else 0
m=[[one,zero],[zero,one]]; sporadic=set()
for n in range(1,N+1):
    iw=1/(WA if w[n-1]=="A" else WB)
    T=[[one-lam*iw,Q([iw])],[-lam,one]]
    m=[[T[0][0]*m[0][0]+T[0][1]*m[1][0],T[0][0]*m[0][1]+T[0][1]*m[1][1]],[T[1][0]*m[0][0]+T[1][1]*m[1][0],T[1][0]*m[0][1]+T[1][1]*m[1][1]]]
    if n<3: continue
    g=(m[0][0]-1).gcd(m[0][1]).gcd(m[1][0]).gcd(m[1][1]-1)
    if g.degree()>0:
        assert g.gcd(g.derivative()).degree()==0, ("gcd not squarefree", n)
    if n in fourF:
        assert g.degree()==fourF[n], ("4F_k count", n, g.degree())
        print(n, g.degree(), "4F", flush=True)
    elif g.degree()>0:
        sporadic.add(n); print(n, g.degree(), g, flush=True)
        if n<=LIMIT:
            assert r==2 and g.degree()==1 and g(WA)==0, ("unexpected double", n)
if expected_sporadic is None:
    print("REPORTED (ratio not tabulated)", N, "sporadic:", sorted(sporadic), flush=True)
else:
    assert {x for x in sporadic if x<=LIMIT}=={x for x in expected_sporadic if x<=min(N,LIMIT)}, sporadic
    print("ASSERTED up to", min(N,LIMIT), "| sporadic:", sorted(sporadic), ("(beyond %d reported only)" % LIMIT) if N>LIMIT else "", flush=True)
