"""Compare f_K(m,n) from the network enumeration with OEIS A219158 (exact minimum squares, all m <= n <= 388).
f_K(m,n) = min over t | gcd(m,n) of best(m/t, n/t) from networks with <= K squares; must equal A219158 whenever
A219158 <= K, and be absent (> K) otherwise.
Exit 0: full agreement. Exit 1: a mismatch. Exit 2: missing or incomplete input (needs best_4 .. best_{K+3})."""
import glob, math, os, sys
import traceback


def _infrastructure_failure(kind, value, tb):  # any uncaught exception is an infrastructure failure: exit 2, never 1
    traceback.print_exception(kind, value, tb)
    sys.stdout.flush()
    os._exit(2)


sys.excepthook = _infrastructure_failure


def require_complete(out_dir: str, K: int) -> None:
    """The enumeration must have finished cleanly for every order: run.sh (or mutant.sh) writes one summary line
    per order, with plantri's count matched and no failed or unresolved case."""
    import os, re
    path = os.path.join(out_dir, "summary.txt")
    if not os.path.isfile(path):
        print(f"no {path}: the enumeration did not finish")
        sys.exit(2)
    done = {}
    for line in open(path):
        m = re.match(r"nv=(\d+) .*graphs=(\d+) .*exact-check-failures=(\d+) unresolved=(\d+)", line)
        if m:
            done[int(m.group(1))] = (int(m.group(2)), int(m.group(3)), int(m.group(4)))
    for nv in range(4, K + 4):
        if nv not in done or done[nv][0] == 0 or done[nv][1] or done[nv][2]:
            print(f"order nv={nv} missing or not clean in {path}")
            sys.exit(2)

K = int(sys.argv[1])
OUT = sys.argv[2] if len(sys.argv) > 2 else "out"
require_complete(OUT, K)
need = [f"{OUT}/best_{nv}.txt" for nv in range(4, K + 4)]
missing = [fn for fn in need if not __import__("os").path.isfile(fn)]
if missing:
    print("missing enumeration files:", missing)
    sys.exit(2)
best = {}
for fn in need:
    for line in open(fn):
        a, b, k = map(int, line.split())
        if k <= K:
            best[(a, b)] = min(best.get((a, b), 99), k)
try:
    vals = [int(l.split()[1]) for l in open("b219158.txt") if l.strip() and not l.startswith("#")]
except (OSError, ValueError, IndexError) as e:
    print("cannot read b219158.txt:", e)
    sys.exit(2)
if len(vals) != 388 * 389 // 2:
    print(f"b219158.txt has {len(vals)} values, expected {388 * 389 // 2}")
    sys.exit(2)
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
if checked_le == 0:
    sys.exit(2)
sys.exit(1 if mism else 0)
