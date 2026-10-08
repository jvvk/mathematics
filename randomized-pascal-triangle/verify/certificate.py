"""Exact rational drift certificates; uses no numerical solver."""
import itertools
import json
import math
from fractions import Fraction as Q
from pathlib import Path
from rays import arrangement, rays

CERTIFICATES={
    'quarter':dict(start=Q(1,4),lam=Q(51,50),
        coef=[Q(1),Q(12,25),Q(1,32),Q(1,5)],
        corr=[Q(1,10),Q(0),Q(-3,100)]),
    'low':dict(start=Q(29,125),lam=Q(5001,5000),
        coef=[Q(1),Q(1249,2500),Q(3,100),Q(557,2500)],
        corr=[Q(999,10000),Q(0),Q(-81,2500)]),
}


def dot(a,b):return sum(x*y for x,y in zip(a,b))


def bernstein(x,cert):
    COEF,LAMBDA,CORR=cert['coef'],cert['lam'],cert['corr']
    a,b,c,d=x
    v=[Q(a+b+c+d,4),Q(abs(a-b)+abs(b-c)+abs(c-d),3),
       Q(abs(a-c)+abs(b-d),2),
       Q(abs(abs(a-b)-abs(b-c))+abs(abs(b-c)-abs(c-d)),2)]
    base=-LAMBDA*dot(COEF,v)+CORR[0]*(a+d-b-c)+CORR[1]*(abs(a-b)+abs(c-d)-2*abs(b-c))
    bb=[base for _ in range(4)]
    for bits in itertools.product([0,1],repeat=3):
        A,B,C=[u+v if z else abs(u-v) for u,v,z in zip([a,b,c],[b,c,d],bits)]
        out=[Q(A+B+C,3),Q(abs(A-B)+abs(B-C),2),Q(abs(A-C)),Q(abs(abs(A-B)-abs(B-C)))]
        k=sum(bits)
        bb[k]+=(dot(COEF,out)+CORR[2]*(A+C-2*B))/math.comb(3,k)
    return bb


def restrict_right(bb,a):
    n=len(bb)-1
    return [sum(Q(math.comb(n-k,i))*a**i*(1-a)**(n-k-i)*bb[k+i] for i in range(n-k+1)) for k in range(n+1)]


def main():
    rr=rays()
    result={'hyperplanes':arrangement(),'certificates':{}}
    for name,cert in CERTIFICATES.items():
        rows=[]
        for r in rr:
            bb=restrict_right(bernstein(r,cert),cert['start'])
            rows.append({'ray':r,'coefficients':[str(b) for b in bb]})
        fails=[row for row in rows if min(map(Q,row['coefficients']))<0]
        minimum=min(Q(b) for row in rows for b in row['coefficients'])
        print(name,'hyperplanes',len(arrangement()),'rays',len(rr),'negative coefficients',len(fails),'minimum',minimum)
        assert not fails
        result['certificates'][name]={'p_interval':[str(cert['start']),'1'],'lambda':str(cert['lam']),
            'potential':[str(c) for c in cert['coef']], 'corrections':[str(c) for c in cert['corr']],
            'rays':rows,'success':not fails,'minimum_coefficient':str(minimum)}
    Path(__file__).with_name('certificate.json').write_text(json.dumps(result,indent=2)+'\n')


if __name__=='__main__':main()
