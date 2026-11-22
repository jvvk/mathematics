"""Audit septic exclusion certificates by integer products and exact fractions.
Does not use the new filter, Smith form, or its integer-kernel computation.
"""
from collections import Counter
from fractions import Fraction as Q
from itertools import combinations, product
from pathlib import Path
import hashlib,json
from audit_sextic import rows_of,mono_div,deg,forced,kappa

HERE=Path(__file__).resolve().parent
PAIRS=list(combinations(range(4),2))

def audit(m=7,source='survivors',tag='fibre_reciprocity'):
 src=HERE/f'm{m}_{source}.json';items=json.loads(src.read_text())
 payload=json.loads((HERE/f'm{m}_{tag}_certificates.json').read_text())
 assert payload['source_sha256']==hashlib.sha256(src.read_bytes()).hexdigest()
 seen=set();counts=Counter()
 for rec in payload['exclusions']:
  ix,why,c=rec['index'],rec['reason'],rec['certificate'];assert ix not in seen;seen.add(ix)
  cfg=items[ix]['cfg'];rows=rows_of(cfg);n=len(cfg)
  if why in ['residual fibre','two-fibre packing']:
   u=c['monomial'];d=mono_div(u,rows);fv=forced(u,cfg);assert d==c['divisor']
  if why=='residual fibre':
   assert deg(d)==3;p,q=c['double_point'],c['residual_point'];assert fv[p][1]>=2
   R=c['relation_rows'];assert R[:4]==rows
   allowed=[]
   for i,j in PAIRS:
    for s in [-1,1]:
     v=[int(k==i)+s*int(k==j) for k in range(4)];e=mono_div(v,rows);dl=deg(e)
     for point,(z,r) in forced(v,cfg).items():
      if dl>0 and r==dl:
       rel=[max(a,0) for a in e];rel[point]-=dl;allowed.append(rel)
   assert all(r in allowed for r in R[4:])
   target=[max(a,0)-2*int(k==p)-int(k==q) for k,a in enumerate(d)]
   assert c['target']==target
   assert [sum(a*r[k] for a,r in zip(c['coefficients'],R)) for k in range(n)]==target
   assert d[q]!=0 or (q!=p and q in fv and fv[q][1]>=2)
  elif why=='two-fibre packing':
   dl=deg(d);assert dl==c['degree'];z=Q(c['value_squared'])
   pts=[(p,r) for p,(v,r) in fv.items() if v==z];assert [list(p) for p in pts]==c['points']
   weights=[r for p,r in pts]
   assert all(sum(r for r,s in zip(weights,sg) if s)>dl or sum(r for r,s in zip(weights,sg) if not s)>dl
              for sg in product([False,True],repeat=len(weights)))
  elif why=='tame reciprocity':
   assert c['pair_order']==[list(p) for p in PAIRS];t=c['skew_coefficients'];T=[[0]*4 for _ in range(4)]
   for (i,j),a in zip(PAIRS,t):T[i][j]=a;T[j][i]=-a
   total=Q(1)
   for point,col in enumerate(cfg):
    mu,e=col[0],col[1:];w=[sum(T[i][j]*e[j] for j in range(4)) for i in range(4)]
    kc=kappa(e,mu);val=Q(1)
    if kc is None:assert not any(w)
    else:
     kap,missing=kc;assert w[missing]==0
     assert sum((1 if e[i]>0 else -1)*w[i] for i in range(4) if i!=missing)==0
     for i in range(4):
      if i!=missing:val*=kap[i]**(-(1 if e[i]>0 else -1)*w[i])
    assert c['local'][point]==dict(exponents=w,factor=str(val));total*=val
   assert total==Q(c['product']) and total!=1
  else:raise AssertionError(why)
  counts[why]+=1
 remaining=[item for ix,item in enumerate(items) if ix not in seen]
 assert remaining==json.loads((HERE/f'm{m}_{tag}_survivors.json').read_text())
 assert Counter(dict(counts,survives=len(remaining)))==Counter(payload['counts'])
 print(f'm={m}: {len(seen)} exclusion certificates audited; {len(remaining)} survivors; {dict(counts)}')


def controls():
 # Actual degree-two x-map on y^2=x(x-1)(x-2): the fibres at x=0 and x=1 are double.
 # Their squared values for f=x+1 are 1 and 4, hence use different packing groups.
 assert all(sum(w)<=2 for w in [[2],[2]])
 # Two forced double points in the two fibres with the same squared value are possible (degree two),
 # but three forced double points cannot fit in two fibres of degree three.
 def feasible(ws,d):
  return any(sum(w for w,s in zip(ws,signs) if s)<=d and sum(w for w,s in zip(ws,signs) if not s)<=d
             for signs in product([False,True],repeat=len(ws)))
 assert feasible([2,2],2) and not feasible([2,2,2],3)
 # Actual tame symbols of f=x, g=y on y^2=x^3-x at (0,0),(1,0),(-1,0),O.
 data=[(2,1,Q(-1),Q(1)),(0,1,Q(1),Q(1)),(0,1,Q(-1),Q(1)),(-2,-3,Q(1),Q(-1))]
 symbols=[Q(-1)**(a*b)*u**b/v**a for a,b,u,v in data]
 assert symbols==[Q(-1),Q(1),Q(-1),Q(1)] and __import__('math').prod(symbols)==1
 print('controls: valid degree-two fibre packing and elliptic tame reciprocity retained; impossible packing rejected')

if __name__=='__main__':
 controls();audit()
 for m in [4,5,6]:audit(m,'configs','fibre_reciprocity_calibration')
