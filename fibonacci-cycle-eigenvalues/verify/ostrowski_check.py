from spec import fibword
s=["B","A"]
while len(s)<22: s.append(s[-1]+s[-2])
f=fibword(20000)
for n in range(1,6001):
    m=n; parts=[]
    for j in range(len(s)-1,0,-1):          # greedy over j>=1, |s_j| = F_{j+1}
        if len(s[j])<=m: parts.append(j); m-=len(s[j])
    assert m==0 and all(a-b>=2 for a,b in zip(parts,parts[1:])), n
    assert "".join(s[j] for j in parts)==f[:n], n
print("prefix_n = s_{j1}...s_{jr} (greedy Zeckendorf, j>=1, gaps>=2) for all n<=6000")
