"""Reproduce the paper's finite checks, using exact integers except sampling CIs.

Usage: python3 verify.py {examples,words,pairs,maxima,samples} [maximum n]
Outputs JSON. Python 3.9+, standard library only.
"""
import itertools
import json
import math
import random
import sys

from diag import cvecs, brute_pairs, alt
from density import check_word
from density4 import word_S, word_T, certify3


def desc(w):
    return {i+1 for i in range(len(w)-1) if w[i]>w[i+1]}


def inverse(w):
    v=[0]*len(w)
    for i,x in enumerate(w,1):
        v[x-1]=i
    return v


def examples():
    S={5,7,8,11,13}; T={2,3,6,9,10,12,13}
    u=word_S(S,14,3); v=word_T(T,14,3)
    assert u == [1,1,1,1,1,2,1,3,4,2,2,5,1,6]
    assert v == [1,1,2,3,1,1,4,1,1,2,5,1,2,6]
    shape=(7,3,1,1,1,1)
    assert check_word(u,S,shape) and check_word(v,T,shape)
    w=[1,4,5,7,14,11,13,10,6,8,9,3,12,2]
    assert desc(w)==S and desc(inverse(w))==T
    cv=cvecs(6)
    ribbon=1 | (1 << 2)  # S={1,3}, alpha=(1,2,3)
    assert (3,3) not in cv[ribbon]
    return {'row_words':[u,v],'shape':shape,'permutation':w,
            'ribbon_123_support':sorted(cv[ribbon]),'missing_partition':[3,3]}


def subsets(n):
    return [{i+1 for i in range(n-1) if mask>>i&1} for mask in range(1<<(n-1))]


def brute_certificates():
    out=[]
    for n in range(2,10):
        actual=set()
        for w in itertools.permutations(range(1,n+1)):
            actual.add((frozenset(desc(w)),frozenset(desc(inverse(w)))))
        count=0
        for S in subsets(n):
            for T in subsets(n):
                if certify3(S,T,n):
                    assert (frozenset(S),frozenset(T)) in actual
                    count+=1
        out.append({'n':n,'f':len(actual),'certified_pairs':count})
    return out


def words(N):
    counts=[]
    for n in range(2,N+1):
        count=0
        for S in subsets(n):
            for b in range(1,n+1):
                for make,c in [(word_S,len(S)-1),(word_T,len(S)-b)]:
                    if c<0 or n-c-b<b:
                        continue
                    w=make(S,n,b)
                    if w is not None:
                        assert check_word(w,S,(n-c-b,b)+(1,)*c),(n,S,b,c,w)
                        count+=1
        counts.append({'n':n,'row_words':count})
    return {'total_row_words':sum(x['row_words'] for x in counts),'by_n':counts}


def dominance(a,b):
    x=y=0
    for i in range(max(len(a),len(b))):
        x+=a[i] if i<len(a) else 0
        y+=b[i] if i<len(b) else 0
        if x>y:
            return False
    return True


def bounds(mask,n):
    cuts=[0]+[i+1 for i in range(n-1) if mask>>i&1]+[n]
    alpha=[b-a for a,b in zip(cuts,cuts[1:])]
    rows=tuple(sorted(alpha,reverse=True))
    cols={}; start=0
    for a in alpha:
        for j in range(start,start+a):
            cols[j]=cols.get(j,0)+1
        start+=a-1
    hi=tuple(sum(c>=i for c in cols.values()) for i in range(1,max(cols.values())+1))
    return rows,hi


def pairs(N):
    out=[]
    for n in range(1,N+1):
        cv=cvecs(n)
        assert len(cv)==1<<(n-1)
        shapes=sorted({sh for v in cv.values() for sh in v})
        tags={s:1<<i for i,s in enumerate(shapes)}
        supports=[sum(tags[s] for s in cv[m]) for m in range(1<<(n-1))]
        intervals=[]
        gaps=0
        for mask in range(1<<(n-1)):
            lo,hi=bounds(mask,n)
            interval=sum(tags[s] for s in shapes if dominance(lo,s) and dominance(s,hi))
            intervals.append(interval)
            assert supports[mask]&~interval==0
            gaps+=supports[mask]!=interval
        realised=0; total=0
        strata={}
        sizes=[bin(m).count('1') for m in range(len(supports))]
        for s,a in enumerate(supports):
            for t in range(s,len(supports)):
                actual=bool(a&supports[t])
                predicted=bool(intervals[s]&intervals[t])
                assert actual==predicted,(n,s,t)
                weight=1 if s==t else 2
                realised+=weight*actual
                total+=weight
                d=abs(sizes[s]-sizes[t])
                den,num=strata.get(d,(0,0))
                strata[d]=(den+weight,num+weight*actual)
        assert total==4**(n-1)
        out.append({'n':n,'pairs_checked':total,'f':realised,'noninterval_supports':gaps,
            'size_difference':{d:{'total':den,'realised':num,'proportion':num/den} for d,(den,num) in strata.items()}})
        print(json.dumps({'progress_n':n,'f':realised}),file=sys.stderr,flush=True)
    return out


def maxima(N):
    out=[]
    for n in range(2,N+1):
        cv=cvecs(n)
        diag={s:sum(x*x for x in v.values()) for s,v in cv.items()}
        best=max(diag.values())
        winners=[s for s,v in diag.items() if v==best]
        assert {alt(n,1),alt(n,2)} <= set(winners)
        if n >= 4:
            assert set(winners)=={alt(n,1),alt(n,2)}
        second=max([v for v in diag.values() if v<best],default=0)
        if n>=4:
            assert 3*second<=2*best
        if n<=8:
            bm,barg=brute_pairs(n)
            assert bm==best
            assert all(s in winners and t in winners for s,t in barg)
        out.append({'n':n,'maximum':best,'second':second,'maximisers':winners,'brute_checked':n<=8})
    n=11; cv=cvecs(n); diag={s:sum(x*x for x in v.values()) for s,v in cv.items()}
    s=sum(1<<(i-1) for i in [2,4,7,9])
    nbr={s^(1<<i) for i in range(n-1)}
    nbr|={s^(3<<i) for i in range(n-2) if (s>>i&1)!=(s>>(i+1)&1)}
    assert diag[s]==1808 and max(diag[t] for t in nbr)==1751
    return {'by_n':out,'local_maximum':{'n':11,'S':[2,4,7,9],'value':diag[s],
        'largest_neighbour':max(diag[t] for t in nbr),'moves':'toggle or adjacent shift'}}


def wilson(k,N):
    z=1.959963984540054
    p=k/N; den=1+z*z/N
    centre=(p+z*z/(2*N))/den
    delta=z*math.sqrt(p*(1-p)/N+z*z/(4*N*N))/den
    return [centre-delta,centre+delta]


def samples():
    rng=random.Random(11); N=20000; out=[]
    for n in [12,13,20,50,100,200,400]:
        ok=0
        for _ in range(N):
            S=frozenset(i for i in range(1,n) if rng.random()<.5)
            T=frozenset(i for i in range(1,n) if rng.random()<.5)
            ok+=certify3(S,T,n)
        fail=N-ok
        out.append({'n':n,'samples':N,'certified':ok,'failures':fail,
            'certified_proportion':ok/N,'failure_95pct_Wilson':wilson(fail,N)})
    return {'seed':11,'generator':'Python random.Random (Mersenne Twister)','results':out}


if __name__=='__main__':
    mode=sys.argv[1]
    maximum=int(sys.argv[2]) if len(sys.argv)>2 else {'words':16,'pairs':13,'maxima':14}.get(mode,0)
    functions={'examples':lambda:examples(),'brute':brute_certificates,'words':lambda:words(maximum),
        'pairs':lambda:pairs(maximum),'maxima':lambda:maxima(maximum),'samples':samples}
    print(json.dumps(functions[mode](),indent=2))
