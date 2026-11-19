"""Remark 1: no poset of the form C1 + U or C1 + C2 + U beats the best fence union F(13), where C1, C2 are
connected posets that are not fences, with at most 11 elements (C2 may be isomorphic to C1), and U is a fence union.
Input: conn_top_k.txt (k = 1..11), the 40 connected posets on k points with the largest f, one per isomorphism
class, as lines "k e(P) #Aut(P) digraph6"; regenerate with
  genposetg k t c q | ../orbits | python3 -I top40.py > conn_top_k.txt
By Lemma 3, f(C1 + U) = C(n, k1) f(C1) f(U) and, for C1 and C2 not isomorphic, f(C1 + C2 + U) = n!/(k1! k2! r!)
f(C1) f(C2) f(U); for C2 = C1 the symmetry swapping the two copies divides by 2. So only the two largest values of
f at each size matter, and the top 40 cover every case. Run: python3 -I n13.py   (prints ALL PASS)."""
import sys
from fractions import Fraction
from math import factorial
from pathlib import Path

N = 13
HERE = Path(__file__).resolve().parent


def zigzag(m):
    E, row = [1], [1]
    for n in range(1, m + 1):
        new = [0]
        for k in range(n):
            new.append(new[-1] + row[n - 1 - k])
        row = new
        E.append(row[-1])
    return E


def fence_max(n_max):
    E = zigzag(n_max)
    types = []
    for m in range(1, n_max + 1):
        w = Fraction(E[m], factorial(m))
        types += [(m, w)] if (m <= 2 or m % 2 == 0) else [(m, w / 2), (m, w / 2)]
    best = [Fraction(0)] * (n_max + 1)
    best[0] = Fraction(1)
    for m, w in types:
        nb = best[:]
        for s in range(n_max + 1):
            if best[s]:
                c = 1
                while s + c * m <= n_max:
                    nb[s + c * m] = max(nb[s + c * m], best[s] * w**c / factorial(c))
                    c += 1
        best = nb
    return [best[n] * factorial(n) for n in range(n_max + 1)]


def decode(g6):
    s = g6.lstrip("&")
    n = ord(s[0]) - 63
    bits = [(ord(c) - 63) >> (5 - i) & 1 for c in s[1:] for i in range(6)]
    return n, {(i, j) for i in range(n) for j in range(n) if bits[i * n + j]}


def is_fence(n, covers):
    """a connected Hasse diagram is a fence iff it is a path on which every inner vertex is a peak or a valley"""
    deg = [0] * n
    for a, b in covers:
        deg[a] += 1
        deg[b] += 1
    if len(covers) != n - 1 or max(deg, default=0) > 2:
        return False
    for v in range(n):
        if deg[v] == 2 and sum(a == v for a, _ in covers) not in (0, 2):
            return False
    return True


F = fence_max(N)
comps = []
for k in range(1, 12):
    rows = [ln.split() for ln in (HERE / f"conn_top_{k}.txt").read_text().splitlines() if ln.strip()]
    if not rows:
        sys.exit(f"conn_top_{k}.txt is empty")
    for kk, e, a, g6 in rows:
        n, covers = decode(g6)
        assert n == int(kk) == k
        if not is_fence(n, covers):
            comps.append((k, Fraction(int(e), int(a)), g6))
best, how = F[N], "fence union"
for i, (k1, f1, g1) in enumerate(comps):
    if k1 <= N:
        v = Fraction(factorial(N), factorial(k1) * factorial(N - k1)) * f1 * F[N - k1]
        if v > best:
            best, how = v, g1
    for k2, f2, g2 in comps[i:]:  # j = i: two copies of the same poset
        if k1 + k2 <= N:
            sym = 2 if g2 == g1 else 1
            v = Fraction(factorial(N), factorial(k1) * factorial(k2) * factorial(N - k1 - k2) * sym) * f1 * f2 * F[N - k1 - k2]
            if v > best:
                best, how = v, g1 + " + " + g2
print(f"F(13) = {F[N]}; best of the other forms = {best} ({how}); {len(comps)} non-fence components read")
ok = F[N] == 54954900 and best == F[N] and how == "fence union"
print("ALL PASS" if ok else "FAILED")
sys.exit(0 if ok else 1)
