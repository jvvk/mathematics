"""Fully exhaustive independent check for a 3-branching counterexample (no shortcuts): BFS max transmission of T,
of the starlike D-tree, and of EVERY (Delta,2)-D-tree (every bar length, every split with each hub having >= 2 pendants).
usage: python3 verify_exhaustive.py 'hub_edges_json' 'arms_json'"""
import itertools, json, sys
from collections import deque

def build(arms, hub_edges):
    adj = {}; cnt = [0]
    def new():
        v = cnt[0]; cnt[0] += 1; adj[v] = []; return v
    hubs = {h: new() for h in set(arms) | {x for e in hub_edges for x in e[:2]}}
    def path(u, w, l):
        prev = u
        for _ in range(l - 1):
            x = new(); adj[prev].append(x); adj[x].append(prev); prev = x
        adj[prev].append(w); adj[w].append(prev)
    for a, b, l in hub_edges: path(hubs[a], hubs[b], l)
    for h, ls in arms.items():
        for l in ls: path(hubs[h], new(), l)
    return adj

def maxtrans(adj):
    best = 0
    for s in adj:
        if len(adj[s]) != 1: continue
        d = {s: 0}; q = deque([s])
        while q:
            x = q.popleft()
            for y in adj[x]:
                if y not in d: d[y] = d[x] + 1; q.append(y)
        best = max(best, sum(d.values()))
    return best

he = [tuple(e) for e in json.loads(sys.argv[1])]; arms = {int(k): v for k, v in json.loads(sys.argv[2]).items()}
D = sorted([e[2] for e in he] + sum(arms.values(), []), reverse=True)
tT = maxtrans(build(arms, he)); n = sum(D) + 1
print("D", D, "k", len(D), "n", n, "T max transmission", tT)
star = maxtrans(build({0: D}, [])); print("starlike", star)
best = None; seen = set()
for bar in sorted(set(D)):
    rest = list(D); rest.remove(bar)
    for m in range(2 ** len(rest)):
        A = tuple(sorted(rest[i] for i in range(len(rest)) if m >> i & 1)); B = tuple(sorted(rest[i] for i in range(len(rest)) if not m >> i & 1))
        if len(A) < 2 or len(B) < 2: continue
        key = (bar,) + tuple(sorted((A, B)))
        if key in seen: continue
        seen.add(key)
        v = maxtrans(build({0: list(A), 1: list(B)}, [(0, 1, bar)]))
        if best is None or v < best[0]: best = (v, bar, A, B)
print("(Delta,2)-D-trees checked", len(seen), "best", best)
print("COUNTEREXAMPLE" if tT < min(star, best[0]) else "NOT a counterexample", "margin", min(star, best[0]) - tT)

# Regression check for the note's tree T (Theorem 1.2): exact values, nonzero exit on any disagreement.
EXPECT = {(53, 23, 21, 9, 9, 9, 1, 1, 1, 1, 1, 1): (5962, 6160, 5971)}
if tuple(D) in EXPECT:
    if (tT, star, best[0]) != EXPECT[tuple(D)]:
        print("CHECK FAILED: expected", EXPECT[tuple(D)], "got", (tT, star, best[0])); sys.exit(1)
    print("CHECK PASSED")
if tT >= min(star, best[0]):
    sys.exit(2)  # the given tree is not a counterexample
