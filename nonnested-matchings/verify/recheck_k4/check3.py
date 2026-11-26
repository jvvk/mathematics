# Claim 3: for each both-gaps<=3 family, margins A,B in 0..MAXM, each boundary edge (i,i+3):
# does EVERY (p,q,r) give an NN4 in S u {star edges of linear length>=4}?  (no wrap edges used)
import json,sys
from common import *
MAXM=int(sys.argv[1])
fams=json.load(open("small16.json"))
def full(F,c): return all((c-d,c) in F and (c,c+d) in F for d in (1,2,3))
allok=True
for idx,F0 in enumerate(fams):
    F0=[tuple(e) for e in F0]; span=max(v for e in F0 for v in e)
    un=sorted(e for e in F0 if e[1]-e[0]==1)
    cs=sorted(c for c in range(1,span+1) if (c-1,c) in un and (c,c+1) in un and not ((c-2,c-1) in un and (c+1,c+2) in un and False))
    # centres = 2nd,4th vertex of unit paths
    verts=sorted({v for e in un for v in e}); cs=[]
    comp=[]; 
    for v in verts:
        if comp and v==comp[-1]+1 and (comp[-1],v) in un: comp.append(v)
        else:
            if comp: cs+=comp[1::2]
            comp=[v]
    cs+=comp[1::2]
    Fs=set(F0)
    ends=[c for c in (cs[0],cs[-1]) if full(Fs,c)]
    works=None; fails_endc=[]
    for A in range(MAXM+1):
        for B in range(MAXM+1):
            n=span+A+B; S=[(a+A,b+A) for a,b in F0]
            good=set()
            for i in range(1,n-2):
                ok=True
                for p,q,r in cyc_triples(i,n):
                    E=S+[norm(e) for e in star(i,p,q,r) if abs(e[0]-e[1])>=4]
                    if not find_nn4(E): ok=False;break
                if ok: good.add(i-A)   # index relative to family coords
            works=good if works is None else works&good
            for c in ends:
                if c-1 not in good: fails_endc.append((A,B,c))
    res_end=[c for c in ends if not any(f[2]==c for f in fails_endc)]
    print(f"fam {idx} span {span} centres {cs} full-star end centres {ends}; end centres whose star (c-1,c+2) works for all margins: {res_end}; all i (family coords) working for all margins: {sorted(works)}",flush=True)
    # reflected version: star (c-2,c+1) at end centre
    if not res_end: allok=False
print("ALL FAMILIES RULED OUT BY (c-1,c+2) AT A FULL-STAR END CENTRE:",allok)
