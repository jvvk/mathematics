"""Compare f_K(m,n) from the network enumeration with OEIS A219158 (exact minimum squares, all m <= n <= 388).
f_K(m,n) = min over t | gcd(m,n) of best(m/t, n/t) from networks with <= K squares; must equal A219158 whenever
A219158 <= K, and be absent (> K) otherwise."""
import glob, math, sys

K = int(sys.argv[1])
OUT = sys.argv[2] if len(sys.argv) > 2 else "out"
best = {}
for fn in glob.glob(f"{OUT}/best_*.txt"):
    for line in open(fn):
        a, b, k = map(int, line.split())
        if k <= K:
            best[(a, b)] = min(best.get((a, b), 99), k)
vals = [int(l.split()[1]) for l in open("b219158.txt") if l.strip() and not l.startswith("#")]
it = iter(vals)
agree = mism = checked_le = 0
bad = []
for n in range(1, 389):
    for m in range(1, n + 1):
        v = next(it)
        g = math.gcd(m, n)
        ours = min((best.get((m // t, n // t), 99) for t in range(1, g + 1) if g % t == 0), default=99)
        if v <= K:
            checked_le += 1
            if ours == v: agree += 1
            else: mism += 1; bad.append((m, n, v, ours))
        elif ours <= K:
            mism += 1; bad.append((m, n, v, ours))
print(f"K={K}: rectangles with A219158 <= K: {checked_le}, agree {agree}; mismatches (either way) {mism}")
print("first mismatches:", bad[:10])
