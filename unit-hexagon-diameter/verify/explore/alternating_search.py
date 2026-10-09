"""Sample alternate vertices, then reconstruct every common-unit-neighbour branch.
This enforces all edge lengths by construction, but remains numerical sampling.
"""
import argparse,json,time,itertools
import numpy as np
from shapely.geometry import Polygon,LineString

def run(n,samples,seed,batch=500000):
    rng=np.random.default_rng(seed);m=n//2;counts=dict(samples=0,branches=0,contained=0,distinct=0,simple=0,proper_crossing=0);witnesses=[];crossed=[];max_error=0.;start=time.monotonic()
    for low in range(0,samples,batch):
        k=min(batch,samples-low);a=rng.random((k,m,2));counts['samples']+=k
        b=np.roll(a,-1,axis=1);v=b-a;d2=np.sum(v*v,axis=2);mid=(a+b)/2
        perp=np.stack((-v[:,:,1],v[:,:,0]),axis=2)
        off=np.sqrt(np.maximum(0,1/d2-.25))[:,:,None]*perp
        for signs in itertools.product([-1,1],repeat=m):
            counts['branches']+=k;odd=mid+off*np.array(signs)[None,:,None]
            keep=np.all((odd>=0)&(odd<=1),axis=(1,2));aa=a[keep];oo=odd[keep];counts['contained']+=len(aa)
            for even,other in zip(aa,oo):
                p=np.empty((n,2));p[::2]=even;p[1::2]=other
                if min(np.linalg.norm(p[i]-p[j]) for i in range(n) for j in range(i))<1e-8:continue
                counts['distinct']+=1;poly=Polygon(p)
                max_error=max(max_error,float(np.max(np.abs(np.sum((p-np.roll(p,-1,axis=0))**2,axis=1)-1))))
                def ori(a,b,c):return (b[0]-a[0])*(c[1]-a[1])-(b[1]-a[1])*(c[0]-a[0])
                crosses=[]
                for i in range(n):
                    for j in range(i+1,n):
                        if j==i+1 or (i,j)==(0,n-1):continue
                        u,v,w,t=ori(p[i],p[(i+1)%n],p[j]),ori(p[i],p[(i+1)%n],p[(j+1)%n]),ori(p[j],p[(j+1)%n],p[i]),ori(p[j],p[(j+1)%n],p[(i+1)%n])
                        if u*v < -1e-12 and w*t < -1e-12:crosses.append([i,j])
                if crosses:
                    counts['proper_crossing']+=1
                    if len(crossed)<5:crossed.append(dict(vertices=p.tolist(),crossing_edges=crosses))
                if poly.is_valid and poly.area>1e-8:
                    counts['simple']+=1;witnesses.append(p.tolist())
        print(json.dumps(dict(n=n,**counts)),flush=True)
    return dict(n=n,seed=seed,seconds=time.monotonic()-start,counts=counts,max_squared_edge_error=max_error,witnesses=witnesses[:10],crossed_examples=crossed)

if __name__=='__main__':
    a=argparse.ArgumentParser();a.add_argument('--n',type=int,nargs='+',default=[6,8]);a.add_argument('--samples',type=int,default=500000);a.add_argument('--seed',type=int,default=481323);a.add_argument('--output',default='alternating-results.json');a=a.parse_args();out=[]
    for n in a.n:
        out.append(run(n,a.samples,a.seed+n))
        with open(a.output,'w') as f:json.dump(out,f,indent=2)
