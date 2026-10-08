"""Break hyperplanes and extreme rays for the four-parent drift functional."""
import itertools
import math
import numpy as np


def canonical(v):
    v=tuple(map(int,v))
    g=math.gcd(*v)
    if not g:return None
    v=tuple(z//g for z in v)
    if next(z for z in v if z)!=abs(next(z for z in v if z)):
        v=tuple(-z for z in v)
    return v


def arrangement():
    e=np.eye(4,dtype=int)
    forms=[[e[i]+e[i+1],e[i]-e[i+1],e[i+1]-e[i]] for i in range(3)]
    planes=set(map(tuple,e))
    for i in range(3):planes.add(tuple(e[i]-e[i+1]))
    for i in range(2):
        planes.add(tuple(e[i]-e[i+2]))
        planes.add(tuple(e[i]-2*e[i+1]+e[i+2]))
    for i,j in [(0,1),(1,2),(0,2)]:
        for a,b in itertools.product(forms[i],forms[j]):
            z=canonical(a-b)
            if z:planes.add(z)
    for a,b,c in itertools.product(*forms):
        z=canonical(a-2*b+c)
        if z:planes.add(z)
    planes=sorted({canonical(z) for z in planes})
    return planes


def det3(m):
    a,b,c=m
    return a[0]*(b[1]*c[2]-b[2]*c[1])-a[1]*(b[0]*c[2]-b[2]*c[0])+a[2]*(b[0]*c[1]-b[1]*c[0])


def rays():
    planes=arrangement()
    result=set()
    for rows in itertools.combinations(planes,3):
        v=canonical([(-1)**i*det3([[r[j] for j in range(4) if j!=i] for r in rows]) for i in range(4)])
        if v and min(v)>=0:result.add(v)
    return sorted(result)


if __name__=='__main__':
    from explore import solve
    rr=rays()
    print('planes',len(arrangement()),'rays',len(rr),flush=True)
    x=np.array(rr,dtype=float)
    for p in [.25,.24,.235,.23]:
        lo,hi=1,1.2
        for _ in range(30):
            mid=(lo+hi)/2
            if solve(x,p,mid).success:lo=mid
            else:hi=mid
        res=solve(x,p,lo-1e-7)
        print(p,lo,res.x if res.success else 'infeasible',flush=True)
