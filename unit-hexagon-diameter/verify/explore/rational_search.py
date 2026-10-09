"""Exact simple-cycle search on rational grids; not a continuum proof."""
import argparse, json, math, time
from collections import Counter

def orient(a,b,c):
    return (b[0]-a[0])*(c[1]-a[1])-(b[1]-a[1])*(c[0]-a[0])

def intersects(a,b,c,d):
    oa,ob,oc,od=orient(a,b,c),orient(a,b,d),orient(c,d,a),orient(c,d,b)
    def on(a,b,p):
        return min(a[0],b[0])<=p[0]<=max(a[0],b[0]) and min(a[1],b[1])<=p[1]<=max(a[1],b[1])
    if oa==0 and on(a,b,c) or ob==0 and on(a,b,d) or oc==0 and on(c,d,a) or od==0 and on(c,d,b):
        return True
    return oa*ob<0 and oc*od<0

def run(m,maxn):
    start=time.monotonic()
    steps=[]
    for x in range(-m,m+1):
        y2=m*m-x*x; y=math.isqrt(y2)
        if y*y==y2:
            steps.append((x,y))
            if y: steps.append((x,-y))
    adj={}
    for x in range(m+1):
        for y in range(m+1):
            ns=[(x+dx,y+dy) for dx,dy in steps if 0<=x+dx<=m and 0<=y+dy<=m]
            if ns: adj[x,y]=ns
    # Iteratively remove leaves: they cannot belong to a cycle.
    while True:
        remove={v for v,ns in adj.items() if len(ns)<2}
        if not remove: break
        adj={v:[u for u in ns if u not in remove] for v,ns in adj.items() if v not in remove}
    counts=Counter(); nodes=0; witnesses={}
    def dfs(path,used):
        nonlocal nodes
        nodes+=1
        a=path[-1]; root=path[0]
        for b in adj[a]:
            if b==root:
                if len(path)<3 or path[1]>path[-1]: continue
                if any(intersects(a,b,path[i],path[i+1]) for i in range(1,len(path)-2)): continue
                counts[len(path)]+=1
                witnesses.setdefault(len(path),list(path))
                continue
            if b<root or b in used or len(path)>=maxn: continue
            if any(intersects(a,b,path[i],path[i+1]) for i in range(len(path)-2)): continue
            dfs(path+[b],used|{b})
    for root in sorted(adj): dfs([root],{root})
    return dict(denominator=m,steps=steps,core_vertices=len(adj),core_edges=sum(map(len,adj.values()))//2,max_sides=maxn,cycles=dict(counts),witnesses=witnesses,search_nodes=nodes,seconds=time.monotonic()-start)

if __name__=='__main__':
    p=argparse.ArgumentParser(); p.add_argument('--grids',nargs='+',type=int,default=[5,13,25,65]);p.add_argument('--max-sides',type=int,default=12);p.add_argument('--output',default='rational-results.json');a=p.parse_args()
    out=[]
    for m in a.grids:
        r=run(m,a.max_sides);out.append(r);print(json.dumps(r),flush=True)
        with open(a.output,'w') as f:json.dump(out,f,indent=2)
