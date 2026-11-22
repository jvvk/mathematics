import math
ps=["0.5","0.4","0.3","0.2","0.15"]
edges=[2**(k/2) for k in range(6,22)]  # 8 .. 1448
print("local slope of log E[len|diam] between successive half-octave bins")
print("bin_center "+" ".join(f"{p:>14}" for p in ps))
data={}
for p in ps:
    rows=[tuple(map(float,l.split())) for l in open(f"big_{p}.txt")]
    B=[]
    for a,b in zip(edges,edges[1:]):
        c=s=s2=ld=0
        for d,cc,ss,ss2 in rows:
            if a<=d<b: c+=cc;s+=ss;s2+=ss2;ld+=cc*math.log(d)
        m=s/c; se=math.sqrt(max(s2/c-m*m,0)/c)
        B.append((ld/c,math.log(m),se/m,c))
    data[p]=B
for i in range(len(edges)-2):
    line=f"{math.exp((data['0.5'][i][0]+data['0.5'][i+1][0])/2):10.0f} "
    for p in ps:
        (x1,y1,e1,_),(x2,y2,e2,_)=data[p][i],data[p][i+1]
        sl=(y2-y1)/(x2-x1); er=math.hypot(e1,e2)/(x2-x1)
        line+=f"  {sl:6.3f}+-{er:5.3f}"
    print(line)
print("Pete delta = %.4f"%((math.sqrt(17)+1)/4))
