from fractions import Fraction as Fr
from spec import fibword
def v2(q):
    if q==0: return 99
    q=Fr(q); v=0; a,b=q.numerator,q.denominator
    while a%2==0: a//=2; v+=1
    while b%2==0: b//=2; v-=1
    return v
x=[Fr(2),Fr(3,2),Fr(1)]  # x_-1,x_0,x_1
while len(x)<16: x.append(x[-1]*x[-2]-x[-3])
print("trace orbit x_-1..:",[str(t) for t in x[:12]])
N=6000; w=fibword(N); m=[[Fr(1),Fr(0)],[Fr(0),Fr(1)]]; rec=[]; hits=[]
for n in range(1,N+1):
    iw=Fr(1) if w[n-1]=="A" else Fr(1,2)
    T=[[1-iw,iw],[Fr(-1),Fr(1)]]
    m=[[T[0][0]*m[0][0]+T[0][1]*m[1][0],T[0][0]*m[0][1]+T[0][1]*m[1][1]],[T[1][0]*m[0][0]+T[1][1]*m[1][0],T[1][0]*m[0][1]+T[1][1]*m[1][1]]]
    v=min(v2(e) for r in m for e in r); h=max(max(abs(Fr(e).numerator),Fr(e).denominator) for r in m for e in r)
    rec.append((n,v,h.bit_length()))
    if m==[[1,0],[0,1]]: print("M_n(1)=I at n=",n); hits.append(n)
print("min v2 / height bits at n=100,200,500,1000,3000,6000:",[rec[i-1] for i in (100,200,500,1000,3000,6000)])
print("max v2 over n>200:",max(r[1] for r in rec[200:]), " n with v2>=0 beyond 106:",[r[0] for r in rec if r[1]>=0 and r[0]>106][:20])

assert hits==[20,33,53,106], hits
assert [str(t) for t in x[:4]]==["2","3/2","1","-1/2"]
print("ASSERTED: M_n(1)=I exactly for n in {20,33,53,106}, n<=6000")
