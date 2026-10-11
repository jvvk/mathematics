"""Is there a rational rescaling q -> c q, c = a/b, making the d^3 instanton numbers integral?
Necessary: c^(p-1) K_p ≡ 8 (mod p^2) for every prime p (d = p level, n_1 = 8c absorbed).
Write K_p/8 = 1 + p t_p (mod p^2) (K_p ≡ 8 mod p holds). Then need q_p(a) - q_p(b) ≡ -t_p (mod p),
q_p = Fermat quotient. Scan |a|, b <= B, gcd 1, p ∤ ab. Report every c passing all primes tested."""
import json
from math import gcd

K = json.load(open("K80.json"))
primes = [p for p in range(3, 80) if all(p % r for r in range(2, int(p**.5) + 1))]
t = {}
for p in primes:
    assert (K[p] - 8) % p == 0, p
    t[p] = (-((K[p] * pow(8, -1, p * p) - 1) % (p * p)) // p) % p
print("targets -t_p:", t)
B = 3000
fq = {p: [((pow(a, p - 1, p * p) - 1) // p) % p if a % p else None for a in range(B + 1)] for p in primes}
hits = []
for a in range(1, B + 1):
    for b in range(1, B + 1):
        if gcd(a, b) != 1:
            continue
        ok = True
        for p in primes:
            if a % p == 0 or b % p == 0:
                continue          # prime divides c: condition is different; skip (weak)
            if (fq[p][a] - fq[p][b]) % p != t[p]:
                ok = False
                break
        if ok:
            hits.append((a, b))
print(f"c = ±a/b with a,b <= {B} satisfying all {len(primes)} primes mod p^2:", hits[:20], len(hits))
