# Own enumeration of uncovered 16-edge NN4-free short families with unit edges (c-1,c),(c,c+1) at 3 centres (P12 shape),
# other 10 edges: ANY edges of length 2 or 3 on [1..N] (5+5 by P9, but we allow any split 10 = a+b with a,b<=6).
import sys, json
from itertools import combinations
from common import *
def families(g1,g2,pad=4):
    c1=4+pad; c2=c1+g1; c3=c2+g2; N=c3+3+pad
    units=[(c-1,c) for c in (c1,c2,c3)]+[(c,c+1) for c in (c1,c2,c3)]
    if find_nn4(units): return [],(c1,c2,c3)
    cand=[(i,i+2) for i in range(1,N-1)]+[(i,i+3) for i in range(1,N-2)]
    # prune candidates that already give NN4 with units
    cand=[e for e in cand if not find_nn4(units+[e])]
    m=len(cand)
    out=[]
    def rec(start,cur):
        if len(cur)==16:
            vs=sorted({v for e in cur for v in e})
            if not any(all(e[0] in C or e[1] in C for e in cur) for C in map(set,combinations(vs,3))):
                out.append(sorted(cur))
            return
        if m-start<16-len(cur): return
        for j in range(start,m):
            e=cand[j]
            # new edge must not create NN4: check cliques containing e
            comp=[f for f in cur if compat(e,f)]
            bad=False
            for x,y,z in combinations(comp,3):
                if compat(x,y) and compat(x,z) and compat(y,z): bad=True;break
            if bad: continue
            rec(j+1,cur+[e])
    rec(0,units)
    return out,(c1,c2,c3)
if __name__=="__main__":
    res={}
    G=int(sys.argv[1])
    for g1 in range(2,G+1):
        for g2 in range(2,G+1):
            fs,cs=families(g1,g2)
            res[f"{g1},{g2}"]={"centres":cs,"fams":fs}
            print(g1,g2,len(fs),flush=True)
    json.dump(res,open("myfams.json","w"))
