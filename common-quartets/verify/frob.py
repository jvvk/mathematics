"""One-tree SAT search for k trees T, s(T), ..., s^(k-1)(T) with no common quartet, s a permutation of order k.

Compact encoding (one tree only): root the tree at leaf r and use rooted triples on the other leaves. A full
rooted-triple system is a rooted binary tree iff every 4-subset is one of the 15 rooted binary 4-leaf trees;
--count re-checks the encoding against (2n-5)!! on small n. Quartets: ra|bc <-> triple bc|a; for a,b,c,d != r,
ab|cd <-> (ab|c and ab|d) or (cd|a and cd|b). Quartet literals occur only negatively in the bans, so the
implication into q is the only direction needed.
"""

import argparse
import sys
import time
from itertools import combinations, permutations, product

from pysat.formula import IDPool
from pysat.solvers import Solver

sys.path.insert(0, __file__.rsplit("/", 1)[0])
from quartets import common_quartets

Split = frozenset


def _clusters(tr) -> list[frozenset[int]]:
    out: list[frozenset[int]] = []

    def rec(t) -> frozenset[int]:
        if isinstance(t, int):
            return frozenset([t])
        s = frozenset().union(*(rec(c) for c in t))
        out.append(s)
        return s

    rec(tr)
    return out


def outgroup(tr, F: tuple[int, ...]) -> int:
    """Index in F of the outgroup of the triple F in the rooted tree tr."""
    for c in sorted(_clusters(tr), key=len):
        I = c & frozenset(F)
        if len(I) == 2:
            return F.index(next(iter(frozenset(F) - I)))
    raise AssertionError(F)


def rooted_patterns() -> set[tuple[int, ...]]:
    pats = set()
    for p in permutations(range(4)):
        for tr in ((((p[0], p[1]), p[2]), p[3]), ((p[0], p[1]), (p[2], p[3]))):
            pats.add(tuple(outgroup(tr, F) for F in combinations(range(4), 3)))
    assert len(pats) == 15
    return pats


def forbidden_cnf(valid: set[tuple[int, ...]]) -> list[list[tuple[int, int]]]:
    """Minimal forbidden partial assignments of size 2-3 (triple index, outgroup index) covering every invalid pattern."""
    out: list[list[tuple[int, int]]] = []
    for size in (2, 3):
        for idx in combinations(range(4), size):
            for vals in product(range(3), repeat=size):
                part = set(zip(idx, vals))
                if any(set(c) <= part for c in out):
                    continue
                ext = (
                    p
                    for p in product(range(3), repeat=4)
                    if all(p[i] == v for i, v in part)
                )
                if all(p not in valid for p in ext):
                    out.append(sorted(part))
    for p in product(range(3), repeat=4):
        hit = any(all(p[i] == v for i, v in c) for c in out)
        assert hit == (p not in valid)
    return out


FORB = forbidden_cnf(rooted_patterns())


def encode_tree(n: int, r: int, pool: IDPool) -> tuple[list[list[int]], dict]:
    """Clauses for one binary tree on range(n) rooted at leaf r; returns (clauses, triple literals)."""
    others = [v for v in range(n) if v != r]
    cls: list[list[int]] = []
    t: dict[tuple[tuple[int, ...], int], int] = {}
    for F in combinations(others, 3):
        lits = [pool.id(("t", F, j)) for j in range(3)]
        for j in range(3):
            t[F, j] = lits[j]
        cls.append(lits)
        cls += [[-lits[a], -lits[b]] for a, b in combinations(range(3), 2)]
    for G in combinations(others, 4):
        Fs = list(combinations(G, 3))
        for c in FORB:
            cls.append([-t[Fs[i], v] for i, v in c])
    return cls, t


def trip(t: dict, u: int, v: int, s: int) -> int:
    """Literal for the rooted triple uv|s."""
    F = tuple(sorted((u, v, s)))
    return t[F, F.index(s)]


def quartet_clauses(
    n: int, r: int, t: dict, pool: IDPool
) -> tuple[list[list[int]], dict]:
    """q[(Q, split)] is implied true whenever the tree displays split on Q."""
    cls: list[list[int]] = []
    q: dict[tuple[tuple[int, ...], Split], int] = {}
    for Q in combinations(range(n), 4):
        if r in Q:
            F = tuple(v for v in Q if v != r)
            for j, og in enumerate(F):
                sp = Split([frozenset([r, og]), frozenset(F) - {og}])
                q[Q, sp] = pool.id(("q", Q, sp))
                cls.append([-t[F, j], q[Q, sp]])
        else:
            a, b, c, d = Q
            for (x, y), (z, w) in (
                ((a, b), (c, d)),
                ((a, c), (b, d)),
                ((a, d), (b, c)),
            ):
                sp = Split([frozenset([x, y]), frozenset([z, w])])
                q[Q, sp] = pool.id(("q", Q, sp))
                cls.append([-trip(t, x, y, z), -trip(t, x, y, w), q[Q, sp]])
                cls.append([-trip(t, z, w, x), -trip(t, z, w, y), q[Q, sp]])
    return cls, q


def decode(n: int, r: int, t: dict, model: set[int]):
    """Rebuild the rooted tree (nested tuples, with r attached at the top) from a model."""
    others = [v for v in range(n) if v != r]

    def og(F):
        return next(F[j] for j in range(3) if t[F, j] in model)

    def build(S: list[int]):
        if len(S) == 1:
            return S[0]
        # The smallest cluster holding a and x is {a, x} plus every y that is not the outgroup of {a, x, y}; the
        # root splits S into the largest proper such cluster and its complement.
        a = S[0]
        rest = [x for x in S if x != a]
        best = None
        for x in rest:
            cl = {a, x} | {
                y for y in rest if y != x and og(tuple(sorted((a, x, y)))) != y
            }
            if len(cl) < len(S) and (best is None or len(cl) > len(best)):
                best = cl
        if best is None:  # a is alone on its side
            best = {a}
        A = sorted(best)
        B = sorted(set(S) - best)
        return (build(A), build(B))

    return (r, build(others))


def count_trees(n: int) -> int:
    pool = IDPool()
    cls, t = encode_tree(n, 0, pool)
    lits = list(t.values())
    c = 0
    with Solver(name="cadical153", bootstrap_with=cls) as s:
        while s.solve():
            m = set(l for l in s.get_model() if l > 0)
            c += 1
            s.add_clause([-v for v in lits if v in m])
    return c


def parse_perm(n: int, spec: str) -> list[int]:
    if spec.startswith("mul:"):
        m = int(spec[4:])
        return [m * x % n for x in range(n)]
    sig = list(range(n))
    for cyc in spec.split(","):
        c = [int(x) for x in cyc.split()]
        for i, v in enumerate(c):
            sig[v] = c[(i + 1) % len(c)]
    return sig


def relabel(tr, f):
    return f[tr] if isinstance(tr, int) else tuple(relabel(c, f) for c in tr)


def build(
    n: int, k: int, sig: list[int], r: int, pool: IDPool
) -> tuple[list[list[int]], dict]:
    """Clauses for: T, sig(T), ..., sig^(k-1)(T) display no common quartet."""
    cls, t = encode_tree(n, r, pool)
    qc, q = quartet_clauses(n, r, t, pool)
    cls += qc
    inv = [0] * n
    for x, y in enumerate(sig):
        inv[y] = x

    def pw(x, e):
        for _ in range(e):
            x = inv[x]
        return x

    # tree number e is sig^e(T): it displays split S on Q iff T displays sig^-e(S) on sig^-e(Q)
    for Q in combinations(range(n), 4):
        a, b, c, d = Q
        for sp in (((a, b), (c, d)), ((a, c), (b, d)), ((a, d), (b, c))):
            clause = []
            for e in range(k):
                pre = tuple(tuple(pw(v, e) for v in part) for part in sp)
                Qe = tuple(sorted(v for part in pre for v in part))
                clause.append(-q[Qe, Split(frozenset(p) for p in pre)])
            cls.append(sorted(set(clause)))
    return cls, t


def search(n: int, k: int, sig: list[int], r: int):
    pool = IDPool()
    cls, t = build(n, k, sig, r, pool)
    print(f"n={n} k={k}: {pool.top} vars, {len(cls)} clauses", flush=True)
    t0 = time.time()
    with Solver(name="cadical153", bootstrap_with=cls) as s:
        res = s.solve()
        dt = time.time() - t0
        if not res:
            return None, dt
        m = set(l for l in s.get_model() if l > 0)
    T = decode(n, r, t, m)
    fam = [T]
    for _ in range(k - 1):
        fam.append(relabel(fam[-1], sig))
    return fam, dt


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("--count", type=int, nargs="*", default=[])
    ap.add_argument("--n", type=int)
    ap.add_argument("--k", type=int)
    ap.add_argument("--perm", help="'mul:3' for x -> 3x mod n, or cycle notation")
    ap.add_argument(
        "--root",
        type=int,
        default=0,
        help="leaf used as root (should be fixed by perm)",
    )
    a = ap.parse_args()
    for n in a.count:
        print(f"n={n}: {count_trees(n)} trees", flush=True)
    if a.n:
        sig = parse_perm(a.n, a.perm)
        assert sorted(sig) == list(range(a.n)), "not a permutation"
        fam, dt = search(a.n, a.k, sig, a.root)
        if fam is None:
            print(f"UNSAT in {dt:.1f}s")
            return
        print(f"SAT in {dt:.1f}s\nT = {fam[0]}")
        print("independent check, common quartets:", len(common_quartets(fam)))


if __name__ == "__main__":
    main()
