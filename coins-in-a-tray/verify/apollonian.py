"""(1) Root quadruples (a,b,c,d) of integral Apollonian packings with outer curvature a = -1:
       a + b + c + d)^2 = 2(a^2+b^2+c^2+d^2), a < 0 <= b <= c <= d, a + b + c >= d (reduced/root condition).
   (2) All curvatures <= BOUND in each such packing (BFS over Descartes reflections d -> 2(a+b+c) - d),
       which curvatures among 2..30 occur, and the residues mod 24."""
from collections import deque
BOUND = 5000
roots = []
for b in range(0, 200):
    for c in range(b, 200):
        for d in range(c, 400):
            a = -1
            if (a + b + c + d) ** 2 == 2 * (a * a + b * b + c * c + d * d) and a + b + c >= d:
                roots.append((a, b, c, d))
print("root quadruples with outer curvature -1:", roots)
for root in roots:
    seen = set(root); q = deque([root]); vis = {tuple(sorted(root))}
    while q:
        t = q.popleft()
        for i in range(4):
            s = list(t); s[i] = 2 * (sum(t) - t[i]) - t[i]
            if s[i] > BOUND or s[i] <= max(t[j] for j in range(4) if j != i) and s[i] in t: continue
            if s[i] <= t[i]: continue          # move away from the root only
            key = tuple(sorted(s))
            if key in vis: continue
            vis.add(key); seen.add(s[i]); q.append(tuple(s))
    cur = sorted(x for x in seen if x > 0)
    print(root, "curvatures 2..30 present:", [k for k in range(2, 31) if k in seen])
    print("   residues mod 24 of curvatures <= BOUND:", sorted({x % 24 for x in cur}))
    print("   missing from 2..30:", [k for k in range(2, 31) if k not in seen])
