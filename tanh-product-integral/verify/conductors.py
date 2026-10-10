"""(1) prod_{k<=rho} cot(pi j k/2m) = s(j) * prod_{k<=m-1-rho} cot(pi j k/2m) with s(j) = +-1 a character-like sign;
(2) conductors occurring in I_n (odd n) vs the asker's lists; (3) rule: a new conductor f > 4 needs some pole family m
with f | 2m and rho' = min(n mod m, m-1-n mod m) >= 1."""
import sys
from math import gcd
import mpmath as mp
from characters import decompose
mp.mp.dps = 30
bad = False
for m in range(2, 30):
    for rho in range(m):
        for j in (x for x in range(1, 2*m) if gcd(x, 2*m) == 1):
            A = mp.fprod(mp.cot(mp.pi*j*k/(2*m)) for k in range(1, rho+1))
            B = mp.fprod(mp.cot(mp.pi*j*k/(2*m)) for k in range(1, m-rho))
            if abs(abs(A) - abs(B)) > 1e-20: bad = True; print("symmetry fails", m, rho, j)
print("(1) |cot product| symmetric under rho -> m-1-rho for m<30:", "FAIL" if bad else "ok")
asker = {3: {1}, 5: {1, 8}, 7: {1, 5, 12}, 9: {1, 7, 8, 12, 16}, 11: {1, 5, 7, 8, 9, 16, 20},
         13: {1, 5, 8, 9, 11, 12, 16, 20, 24}, 15: {1, 5, 7, 8, 9, 11, 12, 13, 20, 24, 28}}
for n in sys.argv[1:] and map(int, sys.argv[1:]) or asker:
    out, _ = decompose(n)
    got = {len(t) for t, K in out.values() if abs(K) > 1e-20}
    fam = {m: (n % m, min(n % m, m-1-n % m)) for m in range(1, n+1) if (n//m) % 2}
    live = {m for m, (r, rp) in fam.items() if rp >= 1}
    print(f"n={n:2d} conductors {sorted(got)} asker {sorted(asker.get(n, set()))} "
          f"{'ok' if got - {1} == asker.get(n, got) - {1} else 'DIFF'}; families m:(rho,rho') {fam}; live {sorted(live)}")
    for f in got - {1, 4}:
        if not any((2*m) % f == 0 for m in live): print("   rule violated for f =", f); bad = True
    if got - {1} != asker.get(n, got) - {1}: bad = True
print("FAIL" if bad else "ALL PASS"); sys.exit(int(bad))
