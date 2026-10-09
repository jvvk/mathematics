"""Exact real-arithmetic feasibility model. 'unknown' is inconclusive."""
import argparse,json,time
import z3

def model(n,domain='square',reflex=None):
    p=[(z3.Real(f'x{i}'),z3.Real(f'y{i}')) for i in range(n)]
    s=z3.SolverFor('QF_NRA')
    for x,y in p:
        if domain=='square': s.add(0<=x,x<=1,0<=y,y<=1)
        else:s.add(2*(x*x+y*y)<=1)
    def orient(a,b,c):return (b[0]-a[0])*(c[1]-a[1])-(b[1]-a[1])*(c[0]-a[0])
    for i in range(n):
        a,b=p[i],p[(i+1)%n]
        s.add((a[0]-b[0])**2+(a[1]-b[1])**2==1)
        prev=p[(i-1)%n]
        s.add((prev[0]-a[0])*(b[0]-a[0])+(prev[1]-a[1])*(b[1]-a[1])>=0)
        if reflex is not None:
            s.add(orient(prev,a,b)<0 if i in reflex else orient(prev,a,b)>0)
        for j in range(i+1,n):
            c=p[j]
            s.add(z3.Or(a[0]!=c[0],a[1]!=c[1]))
        # Adjacent edges cannot overlap (collinear equal edges would repeat a vertex).
        for j in range(i+1,n):
            if j==i+1 or (i==0 and j==n-1):continue
            c,d=p[j],p[(j+1)%n]
            u,v,w,t=orient(a,b,c),orient(a,b,d),orient(c,d,a),orient(c,d,b)
            s.add(z3.Or(z3.And(u>0,v>0),z3.And(u<0,v<0),z3.And(w>0,t>0),z3.And(w<0,t<0),
                z3.And(a[0]<c[0],a[0]<d[0],b[0]<c[0],b[0]<d[0]),
                z3.And(a[0]>c[0],a[0]>d[0],b[0]>c[0],b[0]>d[0]),
                z3.And(a[1]<c[1],a[1]<d[1],b[1]<c[1],b[1]<d[1]),
                z3.And(a[1]>c[1],a[1]>d[1],b[1]>c[1],b[1]>d[1])))
    # Translation to touch both coordinate supports and cyclic choice of bottom vertex.
    if domain=='square':
        s.add(z3.Or(*[y==0 for x,y in p]) if reflex is not None else p[0][1]==0,z3.Or(*[x==0 for x,y in p]))
    else:
        # Rotation makes vertex zero lie on the positive x axis.
        s.add(p[0][1]==0,p[0][0]>0)
    return s,p

if __name__=='__main__':
    a=argparse.ArgumentParser();a.add_argument('--n',type=int,default=6);a.add_argument('--domain',default='square');a.add_argument('--timeout',type=int,default=60000);a.add_argument('--output',default='algebraic-result.json');a.add_argument('--reflex',type=int,nargs='+');a=a.parse_args()
    s,p=model(a.n,a.domain,a.reflex);s.set(timeout=a.timeout)
    with open(a.output+'.smt2','w') as f:f.write(s.to_smt2())
    start=time.monotonic();res=s.check();out=dict(n=a.n,domain=a.domain,reflex=a.reflex,result=str(res),seconds=time.monotonic()-start)
    if res==z3.sat:out['vertices']=[[str(s.model().eval(t)) for t in q] for q in p]
    if res==z3.unknown:out['reason']=s.reason_unknown()
    with open(a.output,'w') as f:json.dump(out,f,indent=2)
    print(json.dumps(out),flush=True)
