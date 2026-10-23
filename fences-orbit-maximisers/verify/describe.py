"""Decode a digraph6 Hasse diagram and describe its components (fence / other)."""
import sys
def parse(s):
    s=s.lstrip('&'); n=ord(s[0])-63; bits=[]
    for c in s[1:]: v=ord(c)-63; bits+= [(v>>(5-i))&1 for i in range(6)]
    return n,[(i,j) for i in range(n) for j in range(n) if bits[i*n+j]]
def components(n,E):
    adj={v:set() for v in range(n)}
    for u,v in E: adj[u].add(v); adj[v].add(u)
    seen=set(); comps=[]
    for v in range(n):
        if v in seen: continue
        st=[v]; c=set()
        while st:
            x=st.pop()
            if x in c: continue
            c.add(x); st+=adj[x]
        seen|=c; comps.append(c)
    return adj,comps
def shape(c,adj,E):
    k=len(c); ce=[(u,v) for u,v in E if u in c]
    if k==1: return 'pt'
    if len(ce)==k-1 and all(len(adj[x])<=2 for x in c):
        # path: alternating iff every vertex is max or min
        ups={u for u,v in ce}; dns={v for u,v in ce}
        if not (ups & dns):
            ends=[x for x in c if len(adj[x])==1]
            lo=sum(1 for x in ends if x in ups)
            return f'Z{k}' + ('' if k%2==0 else ('v' if lo==2 else '^'))
        return f'path{k}'
    return f'other{k}:'+str(sorted(ce))
def describe(s):
    n,E=parse(s); adj,comps=components(n,E)
    return ' + '.join(sorted((shape(c,adj,E) for c in comps),key=lambda t:(-len(t),t)))
if __name__=='__main__':
    for s in sys.argv[1:]: print(s, describe(s))
