"""Negative control for classify.py: for every ordered pair (u, v) of binary words of length n (n <= nmax) and every
block-reversal move u -> v (string conditions from classify.moves), if ok_at accepts at every point then the two
characteristic polynomials must be equal. Counts nontrivial accepted moves (v not u or its reversal).
Usage: python3 soundtest.py nmax [--mut-...]  -> exit 1 if any false acceptance."""
import sys, itertools
import classify as C
from exact import charpoly

nmax = int(sys.argv[1]); acc = nontriv = false = 0; pairs = set()
for n in range(4, nmax + 1):
    words = ["".join(w) for w in itertools.product("01", repeat=n)]
    M = {w: [C.mats(w, t) for t in C.PTS] for w in words}
    cp = {w: charpoly(w) for w in words}
    for u in words:
        for v in words:
            for a, b, la, cuts in C.moves(u, v):
                if all(C.ok_at(M[u][i], M[v][i], n, a, b, la, cuts, t) for i, t in enumerate(C.PTS)):
                    acc += 1
                    if v not in (u, u[::-1]): nontriv += 1; pairs.add((u, v))
                    if cp[u] != cp[v]: false += 1
print("accepted", acc, "nontrivial", nontriv, "distinct nontrivial pairs", len(pairs), "false", false, sorted(C.MUT))
sys.exit(1 if false else 0)
