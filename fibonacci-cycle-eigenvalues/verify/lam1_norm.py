"""lambda=1, weights (1,2). P_j = M_{s_j}(1). 2-adic max-norm  ||P||_2 = 2^{-min v2(entries)}."""
from fractions import Fraction as Fr
def v2(q):
    if q==0: return 10**9
    a,b=q.numerator,q.denominator; v=0
    while a%2==0: a//=2; v+=1
    while b%2==0: b//=2; v-=1
    return v
def mul(X,Y): return [[X[0][0]*Y[0][0]+X[0][1]*Y[1][0],X[0][0]*Y[0][1]+X[0][1]*Y[1][1]],[X[1][0]*Y[0][0]+X[1][1]*Y[1][0],X[1][0]*Y[0][1]+X[1][1]*Y[1][1]]]
lognorm=lambda X: -min(v2(e) for r in X for e in r)
MA=[[Fr(0),Fr(1)],[Fr(-1),Fr(1)]]          # E(1)S at lambda=1
MB=[[Fr(1,2),Fr(1,2)],[Fr(-1),Fr(1)]]      # E(2)S: weight 2 (E(w) has entry 1/w)
P={0:MB,1:MA}
for j in range(2,26): P[j]=mul(P[j-2],P[j-1])   # s_j = s_{j-1}s_{j-2}  =>  M = M_{s_{j-2}} M_{s_{j-1}}
F=[0,1]
while len(F)<40: F.append(F[-1]+F[-2])
for j in range(7,26):
    assert lognorm(P[j])==F[j-7], j
    if j>=9: assert -v2(P[j][0][0]+P[j][1][1])==F[j-7], j
assert all(lognorm(P[j])<=1 for j in range(0,9))
assert [v2(P[j][0][0]+P[j][1][1]) for j in (8,9,10)]==[-1,-1,-2]
assert [lognorm(P[j]) for j in range(0,9)]==[1,0,1,1,0,1,1,0,1]
print("ASSERTED: l_j = F_{j-7} (j=7..25), -v2(tr P_j) = F_{j-7} (j=9..25), l_j <= 1 (j<=8)")
for j in range(0,26):
    tr=P[j][0][0]+P[j][1][1]
    print(j,"len",F[j+1],"log2||P||",lognorm(P[j]),"-v2(tr)",-v2(tr) if tr!=0 else "tr=0", "F_{j-7}" , F[j-7] if j>=7 else "")
