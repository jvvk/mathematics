"""Gessel's max conjecture, diagonal reduction check.

beta(S,T) = sum_lam c_lam(S) c_lam(T), c_lam(S) = #SYT of shape lam with descent set S
(row-word DP: i in S iff r_{i+1} > r_i). Cauchy-Schwarz gives beta(S,T)^2 <= beta(S,S) beta(T,T),
so max beta is on the diagonal. Here: compute beta(S,S) for every S, n <= N, and report the maximisers.
Cross-check: brute force max over all pairs for small n from the same c vectors and from permutations.
"""
import sys, itertools
from collections import defaultdict

def cvecs(n):
    """dict: S (bitmask over 1..n-1) -> dict shape -> count."""
    out = {}
    def step(i, dist, mask):
        # dist: {(shape, last_row): count} after placing i letters
        if i == n:
            c = defaultdict(int)
            for (sh, _), v in dist.items():
                c[sh] += v
            out[mask] = c
            return
        for bit in (0, 1):
            nd = defaultdict(int)
            for (sh, last), v in dist.items():
                for r in range(len(sh) + 1):
                    if (r > last) != bool(bit):
                        continue
                    if r == len(sh):
                        nsh = sh + (1,)
                    elif r == 0 or sh[r - 1] > sh[r]:
                        nsh = sh[:r] + (sh[r] + 1,) + sh[r + 1:]
                    else:
                        continue
                    nd[(nsh, r)] += v
            if nd:
                step(i + 1, nd, mask | (bit << (i - 1)))
    step(1, {((1,), 0): 1}, 0)
    return out

def brute_pairs(n):
    best, arg = 0, []
    cnt = defaultdict(int)
    for w in itertools.permutations(range(n)):
        inv = [0] * n
        for i, x in enumerate(w): inv[x] = i
        s = sum(1 << i for i in range(n - 1) if w[i] > w[i + 1])
        t = sum(1 << i for i in range(n - 1) if inv[i] > inv[i + 1])
        cnt[(s, t)] += 1
    m = max(cnt.values())
    return m, sorted(k for k, v in cnt.items() if v == m)

def alt(n, start):
    return sum(1 << (i - 1) for i in range(start, n, 2))

if __name__ == "__main__":
    N = int(sys.argv[1]) if len(sys.argv) > 1 else 14
    for n in range(2, N + 1):
      cv = cvecs(n)
      diag = {S: sum(v * v for v in c.values()) for S, c in cv.items()}
      m = max(diag.values())
      arg = sorted(S for S, v in diag.items() if v == m)
      second = max(v for v in diag.values() if v < m) if len(set(diag.values())) > 1 else None
      a1, a2 = alt(n, 1), alt(n, 2)
      ok = set(arg) <= {a1, a2}
      line = f"n={n:2d} max beta(S,S)={m} maximisers={[bin(S) for S in arg]} alt-only={ok} 2nd={second}"
      if n <= 8:
          bm, barg = brute_pairs(n)
          # all-pairs max from c vectors
          pm = max(sum(cv[S].get(l, 0) * c for l, c in cv[T].items()) for S in cv for T in cv)
          line += f" | brute max={bm} pairs={[(bin(s), bin(t)) for s, t in barg]} cvec-pairmax={pm}"
      print(line, flush=True)
