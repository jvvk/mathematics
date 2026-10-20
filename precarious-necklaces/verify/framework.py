"""Lower-bound optimisation M_j(k): colour each kept (k-j)-set with a prime, no prime class covering all pairs
of colours; cost = sum over colours x of lcm of the primes on kept sets containing x. Compare with constructions."""
from __future__ import annotations
import itertools, math, sys
from ext import j_precarious

def M(k: int, j: int, primes: tuple[int, ...]) -> tuple[int, dict]:
    s = k - j
    sets = list(itertools.combinations(range(k), s))
    pairs = list(itertools.combinations(range(k), 2))
    covers = {S: {p for p in pairs if set(p) <= set(S)} for S in sets}
    best, arg = None, None
    for col in itertools.product(primes, repeat=len(sets)):
        ok = True
        for q in set(col):
            cov = set().union(*(covers[S] for S, c in zip(sets, col) if c == q))
            if len(cov) == len(pairs): ok = False; break
        if not ok: continue
        cost = sum(math.lcm(*[c for S, c in zip(sets, col) if x in S]) for x in range(k))
        if best is None or cost < best: best, arg = cost, dict(zip(sets, col))
    return best, arg

def blocks(rhythms: list[tuple[str, str, int]], fixed: str) -> str:
    nb = math.prod(p for _, _, p in rhythms)
    return "".join("".join(a + b if j % p == 0 else b + a for a, b, p in rhythms) + fixed for j in range(nb))

w = blocks([("A", "B", 2), ("C", "D", 3)], "E")
print("k=5 j=2 construction: length", len(w), "valid:", j_precarious(w, 2))
for k, j, pr in [(3, 1, (2, 3, 5)), (4, 1, (2, 3, 5)), (4, 2, (2, 3, 5)), (5, 3, (2, 3, 5)), (5, 2, (2, 3, 5)), (5, 1, (2, 3, 5, 7))]:
    b, _ = M(k, j, pr); print(f"M_{j}({k}) over primes {pr}: {b}", flush=True)
