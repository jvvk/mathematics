"""Reachable carry set of the B/B automaton for a given n (hash-based BFS; works for huge n)."""
import sys
def inB(r):
    if r<=0: return False
    while r:
        c=r%3
        if c==0: return False
        c=-1 if c==2 else 1; r=(r-c)//3
    return True
def explore(n):
    seen={0}; st=[0]; acc=False
    while st:
        r=st.pop()
        for d in (-1,1):
            v=r+n*d; c=v%3
            if c==0: continue
            c=-1 if c==2 else 1; r2=(v-c)//3
            if d==1 and (r2==0 or inB(r2)): acc=True
            if r2 not in seen: seen.add(r2); st.append(r2)
    return acc, seen
if __name__=="__main__":
    a,b=int(sys.argv[1]),int(sys.argv[2])
    for k in range(int(sys.argv[3]),int(sys.argv[4])+1):
        n=a*3**k+b; acc,S=explore(n)
        print(k, n, "MEMBER" if acc else "non-member", "reachable carries:",len(S))


def is_member(n):
    """Exact decision with early exit on the first accepting move (non-members explore fully)."""
    seen = {0}; st = [0]
    while st:
        r = st.pop()
        for d in (-1, 1):
            v = r + n*d; c = v % 3
            if c == 0: continue
            c = -1 if c == 2 else 1; r2 = (v - c)//3
            if d == 1 and (r2 == 0 or inB(r2)): return True
            if r2 not in seen: seen.add(r2); st.append(r2)
    return False
