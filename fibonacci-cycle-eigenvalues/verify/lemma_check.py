from spec import fibword
s=["B","A"]
while len(s)<26: s.append(s[-1]+s[-2])
f=fibword(len(s[-1]))
for m in range(3,22):
    U=s[m]; x=s[m-2]; y=s[m-3]+s[m-2]; assert U==x+y
    assert f[:4*len(U)]==U+U+y+x+y+x, m
    assert f[:4*len(U)]==s[m]+s[m-1]+s[m-1]+s[m-2]+s[m-1]+s[m-2]+s[m-2], m
    assert sorted(y[r:]+y[:r] for r in range(len(y))).count(s[m-1])>0  # y is a rotation of s_{m-1}
print("word lemma (Lemma 3.1 of the paper): OK for m=3..21")
