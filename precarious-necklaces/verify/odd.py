"""Odd construction + the r-vector lemma test (MO 515996)."""
from __future__ import annotations
import itertools, math
from neck import precarious, periodic, PRIMES, exhaustive

def odd_construction(m: int) -> str:
    ps, q = PRIMES[:m], PRIMES[m]
    P = math.prod(ps)
    letters = [(chr(65 + 2 * i), chr(66 + 2 * i)) for i in range(m)]
    blk = lambda j: "".join(a + b if j % p == 0 else b + a for (a, b), p in zip(letters, ps))
    return "".join("Z" + "".join(blk(r * q + t) for t in range(q)) for r in range(P))

def r_of(w: str, c: str) -> int:
    u = w.replace(c, "")
    return max(r for r in range(1, len(u) + 1) if len(u) % r == 0 and u == u[: len(u) // r] * r)

def lemma_ok(w: str) -> bool:
    # conjecture: every prime divides r_c for at most two colours c
    rs = [r_of(w, c) for c in set(w)]
    return all(sum(r % p == 0 for r in rs) <= 2 for p in range(2, max(rs) + 1) if all(p % d for d in range(2, p)))

for m in range(1, 4):
    w = odd_construction(m)
    print(f"odd construction k={2*m+1}: length {len(w)}, predicted {math.prod(PRIMES[:m])*(2*m*PRIMES[m]+1)}, precarious={precarious(w)}")
# lemma on all k=3 precarious words, L=14..16
for L in range(14, 17):
    ws = exhaustive(3, L)
    print(f"k=3 L={L}: {len(ws)} precarious, lemma holds on all: {all(lemma_ok(w) for w in ws)}", flush=True)
