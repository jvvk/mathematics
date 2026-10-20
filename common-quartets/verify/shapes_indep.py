"""Count unlabelled unrooted binary trees with n leaves by edge-insertion + AHU canonical form (independent of verify/)."""
import sys
def canon(adj):
    # find centre(s), AHU encoding
    n=len(adj); deg={v:len(adj[v]) for v in adj}; leaves=[v for v in adj if deg[v]<=1]; rem=n
    layer=leaves; removed=set()
    while rem>2:
        rem-=len(layer); nxt=[]
        for v in layer:
            removed.add(v)
            for u in adj[v]:
                if u not in removed:
                    deg[u]-=1
                    if deg[u]==1: nxt.append(u)
        layer=nxt
    centres=[v for v in adj if v not in removed]
    def enc(v,p): return '('+''.join(sorted(enc(u,v) for u in adj[v] if u!=p))+')'
    if len(centres)==1: return enc(centres[0],None)
    a,b=centres; return ''.join(sorted([enc(a,b),enc(b,a)]))
def grow(N):
    start={0:[3],1:[3],2:[3],3:[0,1,2]}; cur={canon(start):start}; counts={3:1}
    for n in range(4,N+1):
        nxt={}
        for adj in cur.values():
            edges={(min(u,v),max(u,v)) for u in adj for v in adj[u]}
            for (u,v) in edges:
                new={k:list(w) for k,w in adj.items()}; m=max(new)+1; l=m+1
                new[u].remove(v); new[v].remove(u)
                new[m]=[u,v,l]; new[u].append(m); new[v].append(m); new[l]=[m]
                c=canon(new)
                if c not in nxt: nxt[c]=new
        cur=nxt; counts[n]=len(cur); print(n,len(cur),flush=True)
grow(int(sys.argv[1]))
