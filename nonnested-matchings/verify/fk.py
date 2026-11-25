"""Exact f_k(n) = max edges of an ordered graph on [n] with no non-nested k-matching (Claude, 2026-11-25).
Edges ij nested with st iff i<s<t<j or s<i<j<t. Non-nested matching: pairwise disjoint, no nested pair.
For each n: find the largest e such that (k-1)n + e edges is satisfiable. Appends results to fk_results.tsv
(checkpoint: skips (k,n) already there). Usage: python3 fk.py k nmin nmax"""
import sys, itertools, time, os
from pysat.solvers import Cadical153
from pysat.card import CardEnc, EncType
from pysat.formula import IDPool

def nested(e, f):
    (i, j), (s, t) = e, f
    return i < s < t < j or s < i < j < t

def crosses(e, f):
    (i, j), (s, t) = e, f
    return i < s < j < t or s < i < t < j

def strongly(M):
    """strongly non-nested: crossing is an equivalence relation whose classes are the blocks."""
    for a, b, c in itertools.permutations(M, 3):
        if crosses(a, b) and crosses(b, c) and not crosses(a, c): return False
    return True

STRONG = os.environ.get("STRONG") == "1"

def nonnested_matchings(n, k):
    for M in _nonnested(n, k):
        if not STRONG or strongly(M): yield M

def _nonnested(n, k):
    """all k-sets of pairwise disjoint, pairwise non-nested edges of K_n on [0,n)."""
    for pts in itertools.combinations(range(n), 2 * k):
        def rec(rem, acc):
            if not rem: yield acc; return
            a = rem[0]
            for b in rem[1:]:
                e = (a, b)
                if any(nested(e, f) for f in acc): continue
                yield from rec([x for x in rem if x not in e], acc + [e])
        yield from rec(list(pts), [])

def solve(n, k, m):
    pool = IDPool(); E = list(itertools.combinations(range(n), 2)); x = {e: pool.id(e) for e in E}
    cl = [[-x[e] for e in M] for M in nonnested_matchings(n, k)]
    cl += CardEnc.atleast([x[e] for e in E], bound=m, vpool=pool, encoding=EncType.seqcounter).clauses
    with Cadical153(bootstrap_with=cl) as s:
        if s.solve():
            mod = set(v for v in s.get_model() if v > 0); return [e for e in E if x[e] in mod]
    return None

if __name__ == "__main__":
    k, a, b = map(int, sys.argv[1:4]); out = "fk_strong_results.tsv" if STRONG else "fk_results.tsv"
    done = set()
    if os.path.exists(out):
        done = {tuple(map(int, l.split()[:2])) for l in open(out) if l[0].isdigit()}
    for n in range(a, b + 1):
        if (k, n) in done: continue
        t0 = time.time(); e = 0; best = solve(n, k, (k - 1) * n)
        assert best is not None, "lower-bound construction should exist"
        while True:
            g = solve(n, k, (k - 1) * n + e + 1)
            if g is None: break
            e += 1; best = g
        line = f"{k}\t{n}\t{(k-1)*n + e}\texcess={e}\t{time.time()-t0:.1f}s\t{best}"
        print(line[:160], flush=True); open(out, "a").write(line + "\n")
