"""Independent direct enumeration of incomplete open cubes and octahedra: connected, not contained in a plane,
not the whole solid, edge subsets up to rotations. Checks the counts by number of edges against Table 1 of
the note. MUTANT=1 identifies mirror images as well, which must fail."""
import itertools, os, numpy as np

MUTANT = os.environ.get("MUTANT") == "1"
EXPECTED = {"cube": [3, 5, 14, 24, 32, 25, 13, 5, 1], "octahedron": [5, 16, 34, 46, 38, 27, 13, 5, 1]}
def rotations():
    mats=[]
    for perm in itertools.permutations(range(3)):
        for signs in itertools.product((1,-1),repeat=3):
            M=np.zeros((3,3),int)
            for i,(p,s) in enumerate(zip(perm,signs)): M[i,p]=s
            if MUTANT or round(np.linalg.det(M))==1: mats.append(M)
    return mats
def solid(name):
    if name=='cube':
        V=[np.array(v) for v in itertools.product((1,-1),repeat=3)]
        E=[(i,j) for i,j in itertools.combinations(range(8),2) if np.sum(V[i]!=V[j])==1]
    else:
        V=[s*np.eye(3,dtype=int)[k] for k in range(3) for s in (1,-1)]
        E=[(i,j) for i,j in itertools.combinations(range(6),2) if np.dot(V[i],V[j])==0]
    return V,E
def count(name):
    V,E=solid(name); R=rotations()
    idx={tuple(v):i for i,v in enumerate(V)}
    eidx={frozenset(e):k for k,e in enumerate(E)}
    perms=[[eidx[frozenset((idx[tuple(M@V[i])],idx[tuple(M@V[j])]))] for i,j in E] for M in R]
    seen=set(); res={}
    for mask in range(1,1<<len(E)):
        if mask in seen: continue
        orb={sum(1<<p[k] for k in range(len(E)) if mask>>k&1) for p in perms}
        seen|=orb
        es=[E[k] for k in range(len(E)) if mask>>k&1]
        vs=sorted({v for e in es for v in e})
        # connected
        adj={v:set() for v in vs}
        for a,b in es: adj[a].add(b); adj[b].add(a)
        st=[vs[0]]; vis={vs[0]}
        while st:
            x=st.pop()
            for y in adj[x]-vis: vis.add(y); st.append(y)
        if len(vis)!=len(vs): continue
        # non-planar: vertex vectors span affine 3-space
        P=np.array([V[v] for v in vs]); 
        if len(vs)<4 or np.linalg.matrix_rank(P[1:]-P[0])<3: continue
        if len(es)==len(E): continue
        res[len(es)]=res.get(len(es),0)+1
    return res
ok = True
for n in ('cube','octahedron'):
    r=count(n); print(n, sum(r.values()), dict(sorted(r.items())))
    ok &= [r.get(k, 0) for k in range(3, 12)] == EXPECTED[n]
print("PASS" if ok else "FAIL")
raise SystemExit(0 if ok else 1)
