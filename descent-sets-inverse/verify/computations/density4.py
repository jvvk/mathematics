"""Exact proof version (DENSITY.md).  Runs R_0..R_{r-1}, lengths al[j]; h = ceil(r/2).
POSITION-SPLIT VERSION. S-word (d=1, e=b-1): R_0 = 1s; R_1 = 2,1..; R_j (j>=2) = leg,(2^k),1.. with all extras in runs j>=h, k <= al[j]-1.
T-word (d=b, e=0):   R_1 and b-1 runs j>=h with al[j-1]>=2 start with 2; other j>=2 start with a leg letter.
Conditions: A = sum_{j<h}(al[j]-1) >= b;  S: sum_{j>=h, j>=2}(al[j]-1) >= b-1;  T: #{j>=h, j>=2, al[j-1]>=2} >= b-1;
shape: n-(s-1)-b >= b.  Claim: conditions => both words are SYT of shape (n-c-b, b, 1^c) with descent sets S, T."""
import itertools, random
from density import runs_of, check_word


def halves(al):
    """Position split: runs starting at a position > n/2 are 'late'; A = #1-letters forced in positions <= n/2."""
    n = sum(al); r = len(al); start, starts = 1, []
    for L in al:
        starts.append(start); start += L
    late = [j for j in range(r) if starts[j] > n // 2]
    h = late[0] if late else r
    A = sum(min(L, max(0, n // 2 - starts[j] + 1)) - (1 if starts[j] <= n // 2 else 0) for j, L in enumerate(al))
    return r, h, A


def word_S(S, n, b):
    al = runs_of(S, n); r, h, A = halves(al)
    if r < 2 or A < b: return None
    slots = [j for j in range(max(h, 2), r)]
    if sum(al[j] - 1 for j in slots) < b - 1: return None
    left, k = b - 1, {}
    for j in slots:
        k[j] = min(al[j] - 1, left); left -= k[j]
    w, leg = [], 3
    for j, L in enumerate(al):
        if j == 0: w += [1] * L
        elif j == 1: w += [2] + [1] * (L - 1)
        else: w += [leg] + [2] * k.get(j, 0) + [1] * (L - 1 - k.get(j, 0)); leg += 1
    return w


def word_T(T, n, b):
    al = runs_of(T, n); r, h, A = halves(al)
    if r < 2 or A < b: return None
    cand = [j for j in range(max(h, 2), r) if al[j - 1] >= 2]
    if len(cand) < b - 1: return None
    two = {1, *cand[: b - 1]}
    w, leg = [], 3
    for j, L in enumerate(al):
        if j == 0: w += [1] * L
        elif j in two: w += [2] + [1] * (L - 1)
        else: w += [leg] + [1] * (L - 1); leg += 1
    return w


def certify3(S, T, n):
    s, t = len(S), len(T)
    if s > t: S, T, s, t = T, S, t, s
    if s == t: return True
    c, b = s - 1, t - s + 1
    if c < 0 or n - c - b < b: return False
    wS, wT = word_S(S, n, b), word_T(T, n, b)
    if wS is None or wT is None: return False
    shape = (n - c - b, b) + (1,) * c
    assert check_word(wS, S, shape), ("S", n, S, T)
    assert check_word(wT, T, shape), ("T", n, S, T)
    return True


def brute_pairs(n):
    pairs = set()
    for w in itertools.permutations(range(n)):
        inv = [0] * n
        for i, v in enumerate(w): inv[v] = i
        pairs.add((frozenset(i + 1 for i in range(n - 1) if w[i] > w[i + 1]),
                   frozenset(i + 1 for i in range(n - 1) if inv[i] > inv[i + 1])))
    return pairs


if __name__ == "__main__":
    for n in range(2, 10):
        P = brute_pairs(n)
        subs = [frozenset(x) for k in range(n) for x in itertools.combinations(range(1, n), k)]
        cert = [(S, T) for S in subs for T in subs if certify3(S, T, n)]
        assert all(p in P for p in cert)
        print(f"n={n}: certified {len(cert)} of f(n)={len(P)}  all certified pairs realizable")
    random.seed(11)
    for n in (12, 13, 20, 50, 100, 200, 400):
        m = 20000
        ok = sum(certify3(frozenset(i for i in range(1, n) if random.random() < .5),
                          frozenset(i for i in range(1, n) if random.random() < .5), n) for _ in range(m))
        print(f"n={n}: random pairs certified {ok}/{m} = {ok/m:.4f}")
