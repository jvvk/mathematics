"""Independent exact checker: standard library only; never imports a game solver."""
from pathlib import Path
from math import comb
import json

def C(n,k):
    return comb(n,k) if 0<=k<=n else 0

def weight(n,i):
    return sum(C(n,j) for j in range(4-i))

def volume(x,n):
    return sum(x[i]*weight(n,i) for i in range(4))

def child(x,q):
    return tuple(q[i]+(x[i-1]-q[i-1] if i else 0) for i in range(4))

def verify():
    data=json.loads(Path(__file__).with_name('counter_certificate.json').read_text())
    a=204262101229170061472237061
    x=(2*a,52,120,0);h=(a,a+26,86,60);depth=106
    assert tuple(data['parent'])==x and tuple(data['halving'])==h and data['depth']==depth
    assert volume(x,106)==(1<<106)-56
    assert volume(x,105)>1<<105
    assert volume(h,105)==(1<<105)-28
    # A row certifies its first-three-coordinate core. Padding then certifies
    # every state with that core whose volume is within the depth budget.
    rows={}
    for row in data['records']:
        assert len(row)==9 and all(type(z) is int for z in row)
        n,aa,bb,cc,dd,*qq=row
        key=(n,aa,bb,cc)
        assert key not in rows
        rows[key]=((aa,bb,cc,dd),tuple(qq))
    certified=set();edges=0
    for key in sorted(rows):
        n,aa,bb,cc=key;state,q=rows[key]
        assert n>=1 and min(state)>=0
        assert volume(state,n)<=1<<n
        assert all(0<=q[i]<=state[i] for i in range(4))
        for query in (q,tuple(state[i]-q[i] for i in range(4))):
            y=child(state,query)
            assert min(y)>=0 and volume(y,n-1)<=1<<(n-1)
            if sum(y[:3])>1:
                assert (n-1,*y[:3]) in certified, (key,y)
            edges+=1
        certified.add(key)
    assert (106,*x[:3]) in certified
    assert rows[(106,*x[:3])][0]==x
    assert rows[(106,*x[:3])][1]==(a,25,112,0)
    assert (106,*h[:3]) in certified
    assert volume(h,106)<=1<<106
    print(f'Winning certificate: {len(rows)} states, {edges} child checks, all passed.')
    print('Certified parent solvable in 106; volume rules out 105.')
    print('Certified halving child solvable in 106.')
    # Prove the halving child is NOT 105-solvable.
    K=sum(h[i]*weight(104,i+1) for i in range(3))
    A=C(104,3);B=C(104,2)
    assert (A,B)==(182104,5356) and A==34*B
    assert ((1<<104)-K)%B==1838
    assert ((1<<103)-105*a-26)%103==35
    assert ((1<<103)-105*a-112)%103==52
    assert all(C(103,j)%103==0 for j in (1,2,3))
    possible=[];rejected=0
    for w in range(87):
        for t in range(61):
            for lam in range(29):
                if (104*w+t+lam-1838)%5356:continue
                ry=(35-w)%103;rz=(52+w)%103
                by=lam+86-w+t;bz=28-lam+w+60-t
                assert ry>by or rz>bz, (w,t,lam,ry,rz,by,bz)
                possible.append((w,t+lam));rejected+=1
    assert set(possible)=={(17,70),(69,18)} and rejected==38
    print('Halving obstruction: only (w,t+lambda)=(17,70),(69,18).')
    print('Each forces residue 69 with available last-class-plus-slack 35.')
    print('All 38 possible (w,t,lambda) triples rejected by exact congruences.')
    print('q(parent)=106; q(halving child)=106; even split costs 107.')
    print('COUNTEREXAMPLE VERIFIED')

if __name__=='__main__':verify()
