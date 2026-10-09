"""Local optimization for equilateral simple polygons. No global certificates."""
import argparse,json,time
import numpy as np
from scipy.optimize import minimize
from shapely.geometry import Polygon,LineString

def run(n,restarts,seed):
    rng=np.random.default_rng(seed);pairs=[(i,j) for i in range(n) for j in range(i+1,n) if j!=i+1 and (i,j)!=(0,n-1)]
    def eq(z):
        p=z[:-1].reshape(n,2);d=p-np.roll(p,-1,axis=0)
        return np.einsum('ij,ij->i',d,d)-z[-1]**2
    def eqjac(z):
        p=z[:-1].reshape(n,2);d=p-np.roll(p,-1,axis=0);a=np.zeros((n,2*n+1))
        for i in range(n):a[i,2*i:2*i+2]=2*d[i];j=(i+1)%n;a[i,2*j:2*j+2]=-2*d[i]
        a[:,-1]=-2*z[-1];return a
    def cross(u,v):return u[...,0]*v[...,1]-u[...,1]*v[...,0]
    def ineq(z):
        p=z[:-1].reshape(n,2);q=np.roll(p,-1,axis=0);out=[]
        for i,j in pairs:
            a,b,c,d=p[i],q[i],p[j],q[j]
            out.append(max(cross(b-a,c-a)*cross(b-a,d-a),cross(d-c,a-c)*cross(d-c,b-c))-1e-12)
        return np.array(out)
    out=[];start=time.monotonic()
    for k in range(restarts):
        angles=np.sort(rng.uniform(0,2*np.pi,n)) if k else np.arange(n)*2*np.pi/n+rng.uniform(0,np.pi)
        radii=rng.uniform(.25,.48,n) if k else np.full(n,.45)
        p=.5+np.column_stack((np.cos(angles),np.sin(angles)))*radii[:,None]
        z=np.r_[p.ravel(),np.mean(np.linalg.norm(p-np.roll(p,-1,axis=0),axis=1))]
        r=minimize(lambda z:-z[-1],z,jac=lambda z:np.r_[np.zeros(2*n),-1.],bounds=[(0,1)]*(2*n)+[(.01,1.42)],constraints=[dict(type='eq',fun=eq,jac=eqjac),dict(type='ineq',fun=ineq)],method='SLSQP',options=dict(maxiter=600,ftol=1e-11))
        p=r.x[:-1].reshape(n,2);poly=Polygon(p);err=float(np.max(np.abs(eq(r.x))));valid=poly.is_valid and poly.area>1e-8 and err<1e-7
        mindist=min((LineString([p[i],p[(i+1)%n]]).distance(LineString([p[j],p[(j+1)%n]])) for i,j in pairs),default=1.)
        out.append(dict(restart=k,success=bool(r.success),valid=bool(valid),edge=float(r.x[-1]),error=err,min_nonadjacent_distance=mindist,vertices=p.tolist(),message=r.message))
        if valid and (k==0 or r.x[-1]>=max(x['edge'] for x in out[:-1] if x['valid']) if any(x['valid'] for x in out[:-1]) else valid):
            print(json.dumps(dict(n=n,restart=k,edge=r.x[-1],separation=mindist)),flush=True)
    return dict(n=n,restarts=restarts,seed=seed,seconds=time.monotonic()-start,runs=out)

if __name__=='__main__':
    a=argparse.ArgumentParser();a.add_argument('--n',type=int,nargs='+',default=[5,6,8]);a.add_argument('--restarts',type=int,default=30);a.add_argument('--seed',type=int,default=481323);a.add_argument('--output',default='continuous-results.json');a=a.parse_args();out=[]
    for n in a.n:
        out.append(run(n,a.restarts,a.seed+n))
        with open(a.output,'w') as f:json.dump(out,f,indent=2)
