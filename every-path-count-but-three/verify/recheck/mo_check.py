def paths(adj, s, t):
    """number of simple s-t paths"""
    def go(v, seen):
        if v == t: return 1
        return sum(go(w, seen | {w}) for w in adj[v] if w not in seen)
    return go(s, {s})

def f(edges, extra=0, x=None, y=None):
    """f(G) for G = edges + `extra` new vertices joined to x and y; returns (f, {pair: count})"""
    V = {v for e in edges for v in e}
    E = list(edges) + [e for i in range(extra) for e in ((x, 100 + i), (y, 100 + i))]
    V |= {100 + i for i in range(extra)}
    adj = {v: [w for e in E for w in e if v in e and w != v] for v in V}
    c = {(u, v): paths(adj, u, v) for u in V for v in V if u < v}
    return max(c.values()), c

FAMILIES = {  # edges of H, x, y, slope, intercept
    "6a+1":  ([(0,1),(1,2),(1,3),(1,4),(2,3),(2,4)], 0, 3, 6, 1),
    "6a+9":  ([(0,1),(0,2),(0,3),(0,4),(0,5),(1,2),(2,3),(2,5),(3,4)], 2, 4, 6, 9),
    "6a+11": ([(0,1),(0,3),(0,4),(0,5),(1,2),(1,5),(2,3),(2,5),(3,4)], 0, 2, 6, 11),
    "2a":    ([(0,1),(1,2)], 0, 2, 2, 0),
}
for name, (H, x, y, s, r) in FAMILIES.items():
    # each pair count is A + B*a once the pair's type exists; read the line off a = 2, 3 and check a = 4
    c2, c3, c4 = (f(H, a, x, y)[1] for a in (2, 3, 4))
    for p in c2:
        B = c3[p] - c2[p]; A = c2[p] - 2 * B
        a0 = 2 if p[0] >= 100 else 1                    # a pair of two new vertices exists only for a >= 2
        assert c4[p] == A + 4 * B and B <= s and A + B * a0 <= r + s * a0, (name, p)  # line <= s*a + r, all a >= a0
    assert all(f(H, a, x, y)[0] == s * a + r for a in (1, 2, 3)), name   # a = 1 directly (some types need a >= 2)
    print(name, "holds for every a >= 1")

K4 = [(0,1),(0,2),(0,3),(1,2),(1,3),(2,3)]
W4 = [(0,1),(1,2),(2,3),(3,0),(4,0),(4,1),(4,2),(4,3)]
G11 = [(0,1),(0,2),(0,5),(1,2),(1,3),(1,4),(1,5),(3,4),(4,5)]
print("K4:", f(K4)[0], " W4:", f(W4)[0], " G11:", f(G11)[0])
