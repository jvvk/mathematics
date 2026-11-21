import numpy as np, sys
def fibword(n):
    w="A"
    while len(w)<n: w="".join("AB" if c=="A" else "A" for c in w)
    return w[:n]
def lap(n,w=None):
    w=w or fibword(n); wt=[1 if c=="A" else 2 for c in w]
    L=np.zeros((n,n))
    for i in range(n):
        j=(i+1)%n; L[i,i]+=wt[i]; L[j,j]+=wt[i]; L[i,j]-=wt[i]; L[j,i]-=wt[i]
    return L,wt
def deficit(n,tol=1e-8):
    ev=np.linalg.eigvalsh(lap(n)[0]); return n-(1+int(np.sum(np.diff(ev)>tol))),ev
if __name__=="__main__":
    for n in [12,20,32,33,52,53]:
        d,ev=deficit(n); w=fibword(n)
        dbl=[round(ev[i],6) for i in range(n-1) if ev[i+1]-ev[i]<1e-8]
        print(n,d,w,dbl)
