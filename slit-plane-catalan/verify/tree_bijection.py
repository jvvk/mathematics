"""An explicit parity bijection proving Shapiro's even-Catalan convolution.
A full binary tree is None (leaf) or (left,right); size counts internal nodes.
ABSENT distinguishes an absent optional tree from the leaf tree.
"""
import sys, os
if not __debug__: sys.exit("refusing to run under python -O: the checks are assertions")
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from functools import lru_cache
from math import comb
ABSENT='absent'
@lru_cache(None)
def size(t):return 0 if t is None else 1+size(t[0])+size(t[1])
@lru_cache(None)
def trees(n):
    if n==0:return (None,)
    return tuple((a,b) for k in range(n) for a in trees(k) for b in trees(n-1-k))
def odd_forward(t,opt):
    """(odd tree, optional even tree) -> (bit, three even trees), removes 1 node."""
    assert size(t)%2==1 and (opt==ABSENT or size(opt)%2==0)
    a,b=t
    if size(a)%2==0:
        return (1,(a,b,None)) if opt==ABSENT else (0,(a,b,opt))
    bit,(u,v,w)=odd_forward(b,opt)
    new=(w,a) if bit==0 else (a,w)
    return 1,(u,v,new)
def odd_inverse(bit,triple):
    u,v,w=triple
    if bit==0:return (u,v),w
    if w is None:return (u,v),ABSENT
    l,r=w
    if size(l)%2==0:subbit,z,a=0,l,r
    else:subbit,z,a=1,r,l
    b,opt=odd_inverse(subbit,(u,v,z))
    return (a,b),opt

def pair_step(a,b):
    """Nontrivial pair of even trees -> two bits and two pairs, removes 2 nodes."""
    assert size(a)%2==size(b)%2==0 and (a is not None or b is not None)
    if a is not None:node,opt=a,b
    else:node,opt=b,ABSENT
    l,r=node
    if size(l)%2==0:orientation,g,t=0,l,r
    else:orientation,g,t=1,r,l
    bit,(u,v,w)=odd_forward(t,opt)
    return (orientation,bit),(g,u),(v,w)
def pair_unstep(color,left,right):
    orientation,bit=color;g,u=left;v,w=right
    t,opt=odd_inverse(bit,(u,v,w))
    node=(g,t) if orientation==0 else (t,g)
    return (None,node) if opt==ABSENT else (node,opt)
def forward(a,b):
    if a is None and b is None:return None
    color,left,right=pair_step(a,b)
    return color,forward(*left),forward(*right)
def inverse(t):
    if t is None:return None,None
    color,l,r=t
    return pair_unstep(color,inverse(l),inverse(r))
def colored_size(t):return 0 if t is None else 1+colored_size(t[1])+colored_size(t[2])

def verify():
    print('EXPLICIT BINARY-TREE SHAPIRO BIJECTION')
    total=0
    for n in range(6):
        images=set();count=0
        for k in range(n+1):
            for a in trees(2*k):
                for b in trees(2*n-2*k):
                    image=forward(a,b)
                    assert inverse(image)==(a,b)
                    assert colored_size(image)==n
                    images.add(image);count+=1
        assert count==len(images)==4**n*comb(2*n,n)//(n+1)
        total+=count
        print('n',n,'pairs',count,'distinct colored trees',len(images),'PASS')
    # Test the subsidiary map on all its objects of total size <=11.
    count=0
    for total_size in range(1,12,2):
        for t in trees(total_size):
            out=odd_forward(t,ABSENT)
            assert odd_inverse(*out)==(t,ABSENT);count+=1
        for odd_size in range(1,total_size+1,2):
            for t in trees(odd_size):
                for opt in trees(total_size-odd_size):
                    out=odd_forward(t,opt)
                    assert odd_inverse(*out)==(t,opt);count+=1
    print('subsidiary odd/optional-even objects, size <=11:',count,'PASS')
    print('total full bijection objects:',total)
if __name__=='__main__':verify()
