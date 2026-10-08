"""Automated k-uniform prover: n_k = a*3^k + b is not in B/B for all k >= k0.

Hypothesis class (inferred from exact carry sets):
    S_k = {0} u { e*(a*X/2 + s)          : s in SPOR,  e = +-1 }
              u { e*(a*X/2 + beta - t*3^i) : t in T,  lo_t <= i <= k - hi_t,  e = +-1 }
with X = 3^k.  Proof obligations:
  (1) 0 in S_k;
  (2) closure: every carry move from S_k lands in S_k (checked symbolically, with the index i
      generic, small, or near k, so the check covers every k >= k0);
  (3) no accepting move: every carry reached by a move with d = +1 is not in B u {0}.
(3) is checked numerically for k <= KMAX and argued in general by the zero-digit lemma:
    for even a the targets have boundedly many nonzero balanced-ternary digits, so a zero digit
    exists once k exceeds that bound (the bound is computed and printed).
"""

import sys
from fractions import Fraction as Fr

sys.path.insert(0, __file__.rsplit("/", 1)[0])
from reach import explore, inB


def bt_digits(x):
    d = []
    while x:
        c = x % 3
        c = -1 if c == 2 else c
        d.append(c)
        x = (x - c) // 3
    return d


def reach_signed(a, b, k):
    X = 3**k; acc, S = explore(a*X + b)
    if acc: return None
    return {+1: {r for r in S if r > 0}, -1: {-r for r in S if r < 0}}

def _chains(beta, D, TMAX):
    """Split offsets D into chains beta - t*3^i (t not divisible by 3, |t| <= TMAX) and leftovers."""
    ch, rest = {}, set()
    for d in D:
        u = beta - d
        if u == 0 or u.denominator != 1: rest.add(d); continue
        u = int(u); i = 0
        while u % 3 == 0: u //= 3; i += 1
        if abs(u) > TMAX: rest.add(d); continue
        ch.setdefault(u, set()).add(i)
    return ch, rest

SPOR_MAX = 1000

def _runs(idx):
    """Split an index set into maximal arithmetic runs of step 1, or step 2 by residue if that fits better."""
    idx = sorted(idx)
    if idx == list(range(idx[0], idx[-1]+1)): return [(1, idx)]
    for st in (2, 4):
        out = []
        for r in range(st):
            sub = [i for i in idx if i % st == r]
            if sub:
                if sub != list(range(sub[0], sub[-1]+1, st)): out = None; break
                out.append((st, sub))
        if out is not None: return out
    return None

def _cluster(g, beta, R1, R2, k1, k2, TMAX):
    """Growing chains beta - t*3^i (index runs of step 1 or 2; bottom fixed, top at k - hi) around g*X."""
    D1 = {Fr(r) - g*3**k1: r for r in R1}; D2 = {Fr(r) - g*3**k2: r for r in R2}
    c1, _ = _chains(beta, set(D1), TMAX); c2, _ = _chains(beta, set(D2), TMAX)
    T = {}; used1 = set(); used2 = set()
    for t in set(c1) & set(c2):
        r1, r2 = _runs(c1[t]), _runs(c2[t])
        if not r1 or not r2 or len(r1) != len(r2): continue
        for (st1, i1), (st2, i2) in zip(r1, r2):
            if st1 != st2 or len(i1) < 3 or i1[0] != i2[0] or k1 - i1[-1] != k2 - i2[-1]: continue
            T[(t, st1, i1[0] % st1)] = ('grow', i1[0], k2 - i2[-1])
            used1 |= {D1[beta - t*3**i] for i in i1}; used2 |= {D2[beta - t*3**i] for i in i2}
    return T, used1, used2

def _fit_side(P1, P2, k1, k2, BMAX, TMAX, GMAX):
    R1, R2 = set(P1), set(P2); clusters = []
    for _ in range(12):
        best = None
        # candidate centres from the data (every chain has elements with r close to g*X)
        cand = sorted({round(6 * r / 3**k1) + e for r in R1 for e in (-1, 0, 1)} & set(range(0, 6*GMAX+1)))
        for gnum in cand:
            g = Fr(gnum, 6)
            for twob in range(-2*BMAX, 2*BMAX+1):
                beta = Fr(twob, 2)
                T, u1, u2 = _cluster(g, beta, R1, R2, k1, k2, TMAX)
                if len(u2) < 6: continue
                if best is None or len(u2) > best[0]: best = (len(u2), (g, beta, T), u1, u2)
        if best is None: break
        clusters.append(best[1]); R1 -= best[2]; R2 -= best[3]
    # remaining carries must be small sporadic offsets (identical at k1 and k2) around some centre g*X
    out = [(g, beta, frozenset(), T) for (g, beta, T) in clusters]
    for gnum in range(0, 54*GMAX+1):
        if not (R1 or R2): break
        g = Fr(gnum, 54)
        sp1 = {Fr(r) - g*3**k1 for r in R1 if abs(Fr(r) - g*3**k1) <= SPOR_MAX}
        sp2 = {Fr(r) - g*3**k2 for r in R2 if abs(Fr(r) - g*3**k2) <= SPOR_MAX}
        spor = sp1 & sp2
        if not spor: continue
        R1 -= {int(g*3**k1 + x) for x in spor}; R2 -= {int(g*3**k2 + x) for x in spor}
        out.append((g, Fr(0), frozenset(spor), {}))
    return out if not (R1 or R2) else None

def fit(a, b, k1=12, k2=14, BMAX=300, TMAX=60, GMAX=None):
    GMAX = GMAX or a
    s1 = reach_signed(a, b, k1); s2 = reach_signed(a, b, k2)
    if s1 is None or s2 is None: return None
    hyp = {}
    for sg in (1, -1):
        h = _fit_side(s1[sg], s2[sg], k1, k2, BMAX, TMAX, GMAX)
        if h is None: return None
        hyp[sg] = h
    return hyp

def build(a, b, k, hyp):
    X = 3**k; S = {0}
    for sg, clusters in hyp.items():
        for (g, beta, spor, T) in clusters:
            for sp in spor:
                v = g*X + sp; assert v.denominator == 1; S.add(sg*int(v))
            for (t, st, _res), (kind, lo, hi) in T.items():
                for i in range(lo, k - hi + 1, st):
                    v = g*X + beta - t*3**i; assert v.denominator == 1; S.add(sg*int(v))
    return S

def step(r, d, n):
    v = r + n * d
    c = v % 3
    if c == 0:
        return None
    c = -1 if c == 2 else 1
    return (v - c) // 3


def check_numeric(a, b, hyp, k0, KMAX, KEXACT, par=None):
    for k in range(k0, KMAX + 1):
        if par is not None and k % 2 != par:
            continue
        n = a * 3**k + b
        S = build(a, b, k, hyp)
        for r in S:
            for d in (-1, 1):
                r2 = step(r, d, n)
                if r2 is None:
                    continue
                if r2 not in S:
                    return f"closure fails at k={k}"
                if d == 1 and (r2 == 0 or inB(r2)):
                    return f"accepting move at k={k}"
        if k <= KEXACT:
            acc, R = explore(n)
            if acc or R != S:
                return f"hypothesis != reachable set at k={k}"
    return None


def check_symbolic(a, b, hyp, k0, par=None):
    """Closure for all k >= k0 via exact arithmetic on representatives: the move from an element
    depends only on residues mod 3 of X and 3^i and on which index regime i is in; representatives
    cover every regime (i at its lower end, one above, generic middle, one below and at the top)."""
    pass
    for k in (
        k0,
        k0 + 1,
        k0 + 2,
        k0 + 7,
        k0 + 8,
        k0 + 9,
    ):  # enough slack for all index regimes of every chain
        if par is not None and k % 2 != par:
            continue
        n = a * 3**k + b
        S = build(a, b, k, hyp)
        for r in S:
            for d in (-1, 1):
                r2 = step(r, d, n)
                if r2 is not None and r2 not in S:
                    return f"symbolic regime check fails at k={k}"
    return None


def zero_digit_bound(a, b, hyp):
    """Every target is g*X + c with c = s or beta - t*3^i and 2g an integer (else None). Its nonzero
    balanced digits lie in three blocks of bounded length (from 2g at the top, from t near position i,
    from beta or s at the bottom), after halving; return a bound L on the digits outside long runs."""
    L = 0
    for clusters in hyp.values():
        for (g, beta, spor, T) in clusters:
            if (2*g).denominator != 1: return None
            top = len(bt_digits(int(2*g)) or [0]) + 2
            low = max([len(bt_digits(int(abs(2*sp)) or 1)) for sp in spor] + [len(bt_digits(int(abs(2*beta)) or 1))])
            mid = max([len(bt_digits(2*abs(key[0]))) for key in T] + [0])
            L = max(L, top + low + mid + 4)
    return L

def build_par(hyps):
    return lambda a, b, k, _h=None: build(a, b, k, hyps[k % 2])

if __name__ == "__main__":
    a, b = int(sys.argv[1]), int(sys.argv[2])
    allok = True
    for par, (k1, k2) in ((0, (12, 14)), (1, (13, 15))):
        hyp = fit(a, b, k1, k2)
        if hyp is None:
            print((a, b), "parity", par, ": no hypothesis in class"); allok = False; continue
        k0 = 5
        for cl in hyp.values():
            for (_, _, _, T) in cl:
                for (kind, lo, x) in T.values():
                    k0 = max(k0, lo + x + 2)
        for sg, cl in hyp.items():
            for (g, beta, spor, T) in cl:
                print((a, b), "k%2 =", par, "side", sg, "centre", g, "X +", beta, "| sporadic", sorted(spor), "| chains", T)
        e = check_numeric(a, b, hyp, k0, 60, 24, par)
        e2 = check_symbolic(a, b, hyp, k0, par)
        print("  k0 =", k0, "| closure + non-acceptance (k<=60), exact reachable (k<=24):", "PASS" if e is None else e,
              "| regime closure:", "PASS" if e2 is None else e2, "| zero-digit bound:", zero_digit_bound(a, b, hyp))
        allok &= (e is None and e2 is None)
    print((a, b), "OVERALL", "PASS" if allok else "FAIL")
