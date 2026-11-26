#!/usr/bin/env python3
"""Finite enumerations only. No generating functions or series manipulations.
Run: python3 codex_check.py
"""
import sys, os
if not __debug__: sys.exit("refusing to run under python -O: the checks are assertions")
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from collections import Counter
from fractions import Fraction as Q
from functools import lru_cache
from itertools import product, permutations
from math import comb, factorial

SQ=((1,0),(-1,0),(0,1),(0,-1))
DG=((1,1),(1,-1),(-1,1),(-1,-1))
def C(n): return comb(2*n,n)//(n+1)
def formula_sq(m,i):
    return Q(comb(2*m,m-i),m) if abs(i)<=m and (m-i)%2==0 else Q(0)

def endpoint_dp(steps,limit,bar=False):
    dp=Counter({(0,0):1}); out=[dp]
    for m in range(1,limit+1):
        nd=Counter()
        for (x,y),v in dp.items():
            for dx,dy in steps:
                a,b=x+dx,y+dy
                if b==0 and (a<0 if bar else a<=0): continue
                nd[a,b]+=v
        dp=nd;out.append(dp)
    return out

def first_passage(limit):
    dp=Counter({(0,0):1});out=[0]
    for m in range(1,limit+1):
        nd=Counter();hits=0
        for (x,y),v in dp.items():
            for dx,dy in SQ:
                a,b=x+dx,y+dy
                if b==0 and a<=0:continue
                if (a,b)==(1,0):hits+=v
                else:nd[a,b]+=v
        dp=nd;out.append(hits)
    return out

def cyclic_dp(steps,limit):
    # k is number of primitive factors, equivalently y=0 visits after start.
    dp=Counter({(0,0,0):1});out=[{}]
    for m in range(1,limit+1):
        nd=Counter()
        for (x,y,k),v in dp.items():
            for dx,dy in steps:
                a,b=x+dx,y+dy
                nd[a,b,k+(b==0)]+=v
        dp=nd; vals=Counter()
        for (x,y,k),v in dp.items():
            if y==0: vals[x]+=Q(v,k)
        out.append(dict(vals))
    return out

@lru_cache(None)
def dyck(n):
    if n==0:return ('',)
    return tuple('U'+a+'D'+b for j in range(n) for a in dyck(j) for b in dyck(n-1-j))
def components(w):
    out=[];start=h=0
    for i,a in enumerate(w):
        h+=(1 if a=='U' else -1)
        if h==0:out.append(w[start:i+1]);start=i+1
    return out

def plane_forest(k,e):
    # k full binary trees, total e internal vertices.
    if k==0:return int(e==0)
    return k*comb(2*e+k,e)//(2*e+k)

def cycles(p):
    seen=set();out=[]
    for i in range(len(p)):
        if i in seen:continue
        a=[];j=i
        while j not in seen:
            seen.add(j);a.append(j);j=p[j]
        out.append(a)
    return out

def canonical(c,inc):
    k=len(c);s=sum(inc[x] for x in c)
    # adjusted heights multiplied by k: k*prefix - s*index.
    vals=[];h=0
    for j,x in enumerate(c):
        vals.append(k*h-s*j);h+=inc[x]
    z=min(vals)
    t=min((j for j,v in enumerate(vals) if v==z),key=lambda j:c[j])
    return c[t:]+c[:t]

def sort_cycles(cy,inc,mutate=False):
    cc=[canonical(c,inc) for c in cy]
    cc.sort(key=lambda c:(Q(sum(inc[x] for x in c),len(c)), -c[0]),reverse=mutate)
    return tuple(x for c in cc for x in c)

def unsort(word,inc):
    # Lower convex minorant with maximal equal-slope faces.
    out=[];left=0;k=len(word)
    while left<k:
        h=0;slopes=[]
        for right in range(left+1,k+1):
            h+=inc[word[right-1]]
            slopes.append((Q(h,right-left),right))
        slope=min(x[0] for x in slopes)
        right=max(j for a,j in slopes if a==slope)
        h=0;record=None;starts=[]
        for j in range(left,right):
            if Q(h)==slope*(j-left):
                label=word[j]
                if record is None or label<record:
                    starts.append(j);record=label
            h+=inc[word[j]]
        starts.append(right)
        out.extend([list(word[a:b]) for a,b in zip(starts,starts[1:])])
        left=right
    return out

def perm_from_cycles(cy,k):
    p=[None]*k
    for c in cy:
        for a,b in zip(c,c[1:]+c[:1]):p[a]=b
    return tuple(p)

def signed_inverse_toggle(w,j):
    # w is a Dyck path; j is empty or one irreducible Dyck path.
    # optional j has sign -; move its component to/from END of w.
    if j:return w+j,''
    cc=components(w)
    return ''.join(cc[:-1]),cc[-1]

def main():
    print('SMALL ENDPOINT COUNTS (complete-state dynamic enumeration)')
    a=endpoint_dp(SQ,21);ab=endpoint_dp(SQ,20,True)
    b=endpoint_dp(DG,20);bb=endpoint_dp(DG,20,True)
    print('n a01 a10 a-11 a11 abar00 b-11 bbar00')
    for n in range(9):
        vals=(a[2*n+1][0,1],a[2*n+1][1,0],a[2*n][-1,1],a[2*n][1,1],ab[2*n][0,0],b[2*n+1][-1,1],bb[2*n][0,0])
        assert vals[0]==4**n*C(n)
        assert vals[1]==C(2*n+1)
        assert vals[2]==(C(2*n)//2 if n else 0)
        assert vals[3]==(4**(n-1)*C(n)+Q(C(2*n),2) if n else 0)
        assert vals[4]==2*4**n*C(n)-C(2*n+1)
        assert vals[5]==2*4**n*C(n)-C(2*n+1)
        assert vals[6]==4**n*C(n)
        print(n,*vals)
    print('DIAGONAL AXIS COUNTS rows n; i=1,...,n')
    for n in range(1,9):
        vals=[b[2*n][2*i,0] for i in range(1,n+1)]
        assert vals==[i*comb(2*i,i)*comb(2*n,n-i)*4**(n-i)//n for i in range(1,n+1)]
        print(n,vals)
    print('VERTICAL BRIDGE AND DYCK CYCLIC WEIGHTS')
    print('r h_r=sum_bridge(1/k) g_r=sum_Dyck(1/k)')
    for r in range(1,8):
        h=Q(0)
        for ups in __import__('itertools').combinations(range(2*r),r):
            ss=set(ups);y=k=0
            for j in range(2*r):
                y+=1 if j in ss else -1;k+=(y==0)
            h+=Q(1,k)
        g=sum((Q(1,len(components(w))) for w in dyck(r)),Q(0))
        assert h==Q(4**r,2*r) and g==Q(comb(2*r,r),2*r)
        print(r,h,g)
    print('CYCLIC WEIGHTS BY COMPLETE-STATE DP')
    sqcy=cyclic_dp(SQ,14);dgcy=cyclic_dp(DG,14)
    for m in range(1,15):
        for i in range(-m,m+1):assert sqcy[m].get(i,0)==formula_sq(m,i)
        if m%2==0:
            r=m//2
            for j in range(-r,r+1):assert dgcy[m].get(2*j,0)==Q(4**r*comb(2*r,r+j),2*r)
    print('square all endpoints through length 14: PASS')
    print('diagonal all endpoints through length 14: PASS')
    # Independent enumeration of every word through length 8.
    total=0
    for m in range(1,9):
        cy=Counter();sl=Counter();ba=Counter()
        for w in product(SQ,repeat=m):
            x=y=k=0;good=weak=True
            for dx,dy in w:
                x+=dx;y+=dy
                if y==0:
                    k+=1
                    good &= x>0;weak &= x>=0
            if y==0:cy[x]+=Q(1,k)
            if good:sl[x,y]+=1
            if weak:ba[x,y]+=1
            total+=1
        assert dict(cy)==sqcy[m] and sl==a[m] and ba==ab[m]
    print('independent square words checked:',total)
    print('LABELED CYCLE SORT / LOWER CONVEX MINORANT')
    cases=objects=0;mutation_witness=None
    for k in range(1,6):
        pp=list(permutations(range(k)));pc=[cycles(p) for p in pp]
        for inc in product(range(-2,3),repeat=k):
            for mode in ('zero','positive'):
                good=[]
                for p in pp:
                    h=0;ok=True
                    for x in p:
                        h+=inc[x]
                        ok &= h>=0 if mode=='zero' else h>0
                    if ok and (mode!='zero' or h==0):good.append(p)
                images=[]
                for p,cy in zip(pp,pc):
                    sums=[sum(inc[x] for x in c) for c in cy]
                    ok=all(s==0 for s in sums) if mode=='zero' else all(s>0 for s in sums)
                    if not ok:continue
                    w=sort_cycles(cy,inc)
                    assert perm_from_cycles(unsort(w,inc),k)==p
                    images.append(w);objects+=1
                    if mutation_witness is None:
                        bad=sort_cycles(cy,inc,True)
                        if perm_from_cycles(unsort(bad,inc),k)!=p:
                            mutation_witness=(inc,p,bad)
                assert len(images)==len(set(images)) and set(images)==set(good)
                cases+=1
    print('increment lists/modes:',cases,'permutation objects:',objects,'PASS')
    assert mutation_witness is not None
    print('mutation reverse cycle order rejected:',mutation_witness)
    print('DYCK INVERSE INVOLUTION')
    checked=0
    for m in range(1,9):
        for jsize in range(m+1):
            jj=[''] if jsize==0 else ['U'+w+'D' for w in dyck(jsize-1)]
            for w in dyck(m-jsize):
                for j in jj:
                    out=signed_inverse_toggle(w,j)
                    assert signed_inverse_toggle(*out)==(w,j)
                    assert bool(j)!=bool(out[1])
                    checked+=1
    print('all D x (empty - primitive D) objects, size <=8:',checked,'PASS')
    print('SIGNED PAIRS, FIRST-RETURN COUNTS, AND SHAPIRO')
    for n in range(9):
        H=sum(C(2*k)*C(2*n-2*k) for k in range(n+1))
        K=sum(C(2*k+1)*C(2*n-2*k-1) for k in range(n))
        L=sum((-1)**j*C(j)*C(2*n-j) for j in range(2*n+1))
        assert L==ab[2*n][0,0]==H-K
        assert C(2*n+1)==H+K and a[2*n+1][0,1]==H
        assert H==4**n*C(n)
        # Primitive slit loops close strict paths. Recompute through convolution.
        primitive=2*a[2*n+1][0,1]+a[2*n+1][1,0]
        assert primitive==2*C(2*n+1)+L
    print('all identities through n=8: PASS')
    print('DECORATED-BRIDGE CYCLES FOR 237(d)')
    for r in range(1,9):
        for j in range(1,r+1):
            decorated=Q(4**j,2*j)*plane_forest(2*j,r-j)*4**(r-j)
            assert decorated==Q(4**r*comb(2*r,r+j),2*r)
    print('all r<=8, 1<=j<=r: PASS')
    print('FIRST PASSAGE, 236(c), AND THE TWO POSITIVE CYCLE CASES')
    fp=first_passage(21)
    for n in range(10):
        m=2*n+1
        assert fp[m]==C(2*n)
        if n:assert fp[m]==2*a[2*n][-1,1]
        # A first hit of (1,0), then a loop shifted from the weak slit.
        renewal=sum(fp[j]*ab[m-j][0,0] for j in range(1,m+1))
        assert renewal==a[m][1,0]
    for n in range(1,9):
        K=sum(C(2*k+1)*C(2*n-2*k-1) for k in range(n))
        cyclic_two=formula_sq(2*n,2)
        if 2*n<len(sqcy):assert cyclic_two==sqcy[2*n][2]
        assert a[2*n][2,0]==cyclic_two+Q(K,2)
        assert cyclic_two==Q(C(2*n+1),2)-C(2*n)
        assert a[2*n+1][1,0]==a[2*n][2,0]+2*a[2*n][1,1]
    print('first-passage identities through n=9; axis/local identities through n=8: PASS')
    print('PERIODIC CYCLES: MARKING AND HORIZONTAL DELETION')
    for m in range(2,8):
        codes={}
        for w in product(SQ,repeat=m):
            y=0;heights=[]
            for dx,dy in w:heights.append(y);y+=dy
            if y:continue
            v=sum(dy!=0 for dx,dy in w)//2
            if not v:continue
            h=m-2*v;e=sum(dx==1 for dx,dy in w)
            for j,(dx,dy) in enumerate(w):
                if not dy:continue
                code=(w[j:]+w[:j],-heights[j])
                codes.setdefault((v,h,e),set()).add(code)
        for (v,h,e),ss in codes.items():
            assert len(ss)==4**v*comb(m-1,h)*comb(h,e)
            for word,baseline in ss:
                vertical=tuple(z for z in word if z[1])
                gaps=[];pos=-1
                for z in word:
                    if z[1]:gaps.append([]);pos+=1
                    else:gaps[pos].append(z)
                rebuilt=[]
                for step,gap in zip(vertical,gaps):rebuilt.extend((step,*gap))
                assert tuple(rebuilt)==word
        print('length',m,'marked cyclic objects',sum(map(len,codes.values())),'PASS')
    # Deliberately corrupt independent parts, and require rejection.
    mutants={
      'allow_origin_in_strict_slit': endpoint_dp(SQ,3,True)[3][0,1]!=a[3][0,1],
      'erase_sign_on_second_Dyck_path': sum(C(j)*C(2-j) for j in range(3))!=ab[2][0,0],
      'replace_vertical_4_by_3': Q(3,2)!=sqcy[2][0]-Q(1),
      'drop_two_cycle_colors': Q(comb(4,2),4)!=sqcy[2][0],
      'reverse_cycle_order': mutation_witness is not None,
      'forget_Shapiro_color_bit': len({None if z is None else (z[0][0],z[1],z[2]) for z in
        (__import__('tree_bijection').forward(a,b) for k in range(2) for a in __import__('tree_bijection').trees(2*k)
         for b in __import__('tree_bijection').trees(2-2*k))}) != 4,
    }
    assert all(mutants.values())
    for name,v in mutants.items():print('mutation',name,': REJECTED' if v else 'MISSED')
    print('ALL CHECKS PASSED')

if __name__=='__main__':main()
