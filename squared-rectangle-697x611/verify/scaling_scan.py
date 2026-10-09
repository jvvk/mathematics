"""Minimal squaring conjecture f(t m, t n) = f(m, n): search for proven counterexamples within the enumeration.
best[(a,b)] = fewest squares over reduced tilings of shape a x b (complete for <= K squares, sides <= 1500).
f(m,n) (if <= K) = min over t | gcd(m,n) of best[(m/t, n/t)]. A rectangle R = (a,b) with f(R) = k <= K and a proper
divisor-scaled base (a/t, b/t) whose f exceeds k (i.e. no tiling of the base with <= k squares) is a counterexample;
it is PROVEN if k <= K, since the base then provably needs > k squares."""
import glob, math, sys
K = int(sys.argv[1])
best = {}
for fn in glob.glob("out/best_*.txt"):
    for l in open(fn):
        a, b, k = map(int, l.split())
        if k <= K: best[(a, b)] = min(best.get((a, b), 99), k)
def f(m, n):
    m, n = min(m, n), max(m, n); g = math.gcd(m, n)
    return min((best.get((m // t, n // t), 99) for t in range(1, g + 1) if g % t == 0), default=99)
hits = []
for (a, b), k in best.items():
    g = math.gcd(a, b)
    if g == 1: continue
    for t in range(2, g + 1):
        if g % t == 0:
            fb = f(a // t, b // t)
            if fb > k: hits.append((a // t, b // t, t, fb if fb < 99 else f">{K}", a, b, k))
hits.sort(key=lambda h: (h[0] * h[1], h))
print(f"K={K}: reduced shapes {len(best)}; counterexamples (base m x n, factor t, f(base), scaled a x b, f(scaled)):")
for h in hits[:40]: print(h)
print("total", len(hits))
