from itertools import combinations
def compat(e,f):
    a,b=e; c,d=f
    if len({a,b,c,d})<4: return False
    if a<c<d<b or c<a<b<d: return False
    return True
def find_nn4(edges):
    edges=list(dict.fromkeys(edges)); m=len(edges)
    adj=[0]*m
    for i in range(m):
        for j in range(i+1,m):
            if compat(edges[i],edges[j]): adj[i]|=1<<j; adj[j]|=1<<i
    for i in range(m):
        ci=adj[i]>>(i+1)<<(i+1)
        x=ci
        while x:
            j=(x&-x).bit_length()-1; x&=x-1
            cij=ci&adj[j]>>(j+1)<<(j+1)
            y=cij
            while y:
                k=(y&-y).bit_length()-1; y&=y-1
                z=cij&adj[k]>>(k+1)<<(k+1)
                if z:
                    l=(z&-z).bit_length()-1
                    return [edges[i],edges[j],edges[k],edges[l]]
    return None
def is_nn4(M):
    return len(M)==4 and all(compat(e,f) for e,f in combinations(M,2))
def star(i,p,q,r):
    return [(i,i+3),(i+1,p),(i+2,q),(i+3,r),(p,i),(q,i+1),(r,i+2)]
def norm(e): return (min(e),max(e))
def cyc_triples(i,n):
    order=list(range(i+4,n+1))+list(range(1,i))
    return combinations(order,3)
