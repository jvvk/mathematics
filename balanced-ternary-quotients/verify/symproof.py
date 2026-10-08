"""All-k symbolic closure check for a fitted hypothesis (one parity class of k at a time).

Carries are linear forms A*X + B*Y + C (X = 3^k, Y = 3^i). For k >= k0 in the given parity class,
every element of the hypothesised set S_k falls in one of finitely many regimes:
  sporadic      e*(g*X + s)                               (X symbolic)
  chain small   e*(g*X + beta - t*3^i), i explicit small  (X symbolic)
  chain generic e*(g*X + beta - t*Y), Y = 3^i symbolic, i in [L, k - U] with fixed parity of i
  chain top     e*(g*X + beta - t*X/3^j), j explicit small
For each regime and move d = +-1: the output digit is v mod 3, computed 3-adically (every term with
X or Y is divisible by 3 because v3(X) and v3(Y) are large and denominators divide 6); the new carry
r' = (v - digit)/3 must be an element of S_k in some regime, matched by comparing coefficients and
checking index range and parity. If every case matches, S_k is closed for ALL k >= k0 of that parity.
Non-acceptance (moves with d = +1 never land in B u {0}) is handled separately.
"""

import sys
from fractions import Fraction as Fr

sys.path.insert(0, __file__.rsplit("/", 1)[0])

MARGIN = 6  # generic window keeps this many indices away from each chain end


def mod3(c):
    """Residue in {0,1,2} of a rational with denominator coprime to 3."""
    assert c.denominator % 3 != 0
    return (c.numerator * pow(c.denominator, -1, 3)) % 3


def bounds(hyp):
    los = [lo for cl in hyp.values() for (_, _, _, T) in cl for (_, lo, _) in T.values()] or [0]
    his = [hi for cl in hyp.values() for (_, _, _, T) in cl for (_, _, hi) in T.values()] or [0]
    return max(los) + MARGIN, max(his) + MARGIN          # generic regime: L <= i <= k - U

def elements(hyp, par):
    """Regimes of S_k for k of parity par, with global generic window L <= i <= k - U."""
    L, U = bounds(hyp); out = [(1, Fr(0), Fr(0), 0, 'spor', None)]   # the start carry 0
    for sg, clusters in hyp.items():
        for (g, beta, spor, T) in clusters:
            for s in spor:
                out.append((sg, g, s, 0, 'spor', None))
            for (t, st, res), (kind, lo, hi) in T.items():
                for i in range(lo, L):
                    if (i - lo) % st == 0: out.append((sg, g, beta, t, 'small', (i, st, lo, hi)))
                for j in range(hi, U):
                    if st == 1 or (par - j - lo) % st == 0: out.append((sg, g, beta, t, 'top', (j, st, lo, hi)))
                for ipar in ((0, 1) if st == 1 else (lo % 2,)):
                    out.append((sg, g, beta, t, 'gen', (ipar, st, lo, hi)))
    return out

def value_form(el):
    """Return (A, B, C): value = A*X + B*Y + C with Y = 3^i (gen only); small/top folded into A, C."""
    sg, g, c0, t, kind, info = el
    if kind == "spor":
        return (sg * g, Fr(0), sg * c0)
    if kind == "small":
        i = info[0]
        return (sg * g, Fr(0), sg * (c0 - t * 3**i))
    if kind == "top":
        j = info[0]
        return (sg * (g - Fr(t, 3**j)), Fr(0), sg * c0)
    return (sg * g, Fr(-sg * t), sg * c0)


def matches(r, el_from, hyp, par):
    """Is carry r = (A, B, C) an element of S_k for all k in the regime of el_from?"""
    A, B, C = r
    for sg, clusters in hyp.items():
        for g, beta, spor, T in clusters:
            # sporadic
            if B == 0 and A == sg * g and (sg * C) in spor:
                return True
            for (t, st, res), (kind, lo, hi) in T.items():
                # generic source -> generic target with index i-1 (Y' = Y/3)
                if B != 0 and el_from[4] == "gen":
                    ipar = el_from[5][0]
                    if A == sg * g and C == sg * beta and B == Fr(-sg * t, 3):
                        newpar = (ipar - 1) % 2
                        if st == 1 or newpar == lo % 2:
                            return True
                if B == 0:
                    # small explicit index
                    for i in range(lo, bounds(hyp)[0] + 2):
                        if (
                            (i - lo) % st == 0
                            and A == sg * g
                            and C == sg * (beta - t * 3**i)
                        ):
                            return True
                    # top index k - j
                    for j in range(hi, bounds(hyp)[1] + 2):
                        if (
                            (st == 1 or (par - j - lo) % st == 0)
                            and C == sg * beta
                            and A == sg * (g - Fr(t, 3**j))
                        ):
                            return True
    return False


def closure_all_k(a, b, hyp, par):
    fails = []
    for el in elements(hyp, par):
        A, B, C = value_form(el)
        for d in (-1, 1):
            vA, vB, vC = A + d * a, B, C + d * b
            dig = mod3(vC)  # X- and Y-terms vanish mod 3 (high 3-adic valuation)
            if dig == 0:
                continue
            dig = -1 if dig == 2 else 1
            r = (vA / 3, vB / 3, (vC - dig) / 3)
            if not matches(r, el, hyp, par):
                fails.append((el, d, r))
    return fails


def mutate(hyp):
    """Corrupt a hypothesis: drop the first chain of the first cluster on side +1."""
    import copy
    h = copy.deepcopy(hyp)
    for sg in h:
        for n, (g, beta, spor, T) in enumerate(h[sg]):
            if T:
                T2 = dict(T); T2.pop(next(iter(T2))); h[sg][n] = (g, beta, spor, T2); return h
    return h

if __name__ == "__main__" and not (len(sys.argv) > 3 and sys.argv[3] == "cert"):
    from prover import fit

    a, b = int(sys.argv[1]), int(sys.argv[2])
    ok = True
    for par, (k1, k2) in ((0, (12, 14)), (1, (13, 15))):
        hyp = fit(a, b, k1, k2)
        if hyp is None:
            print((a, b), "parity", par, "no hypothesis")
            ok = False
            continue
        f = closure_all_k(a, b, hyp, par)
        print(
            (a, b),
            "parity",
            par,
            "symbolic all-k closure:",
            "PASS" if not f else f"FAIL ({len(f)} cases)",
        )
        for x in f[:4]:
            print("   ", x)
        ok &= not f
        fm = closure_all_k(a, b, mutate(hyp), par)
        print("    mutation (drop a chain) detected:", bool(fm))
    print((a, b), "SYMBOLIC OVERALL", "PASS" if ok else "FAIL")


# ---------------- non-acceptance for all k, and the final certificate ----------------

def bt_len(n):
    n = abs(int(n)); L = 0
    while n: c = n % 3; c = -1 if c == 2 else c; n = (n - c) // 3; L += 1
    return L

def split_power(A):
    """A*X = P * 3^(k-m) with P integer: return (P, m)."""
    m = 0
    while (A*3**m).denominator != 1:
        m += 1
        assert m < 12, f"coefficient {A} not of the form P/3^m"
    return int(A*3**m), m

def nonaccept_all_k(a, b, hyp, par):
    """For every d = +1 move, the target r' = P*3^(k-m) + Q*3^i + R has a zero balanced digit (or is
    <= 0) for all k >= Kstar. Returns (ok, Kstar, problems)."""
    Kstar = 0; probs = []
    L, U = bounds(hyp)
    for el in elements(hyp, par):
        A, B, C = value_form(el)
        vA, vB, vC = A + a, B, C + b
        dig = mod3(vC)
        if dig == 0: continue
        dig = -1 if dig == 2 else 1
        rA, rB, rC = vA/3, vB/3, (vC - dig)/3
        if rC.denominator != 1: probs.append((el, 'nonint C')); continue
        P, m = split_power(rA); R = int(rC)
        if P < 0 or (P == 0 and rB == 0 and R <= 0):
            continue                                   # negative or zero-free impossible: not in B u {0}? (0 excluded below)
        if P == 0 and rB == 0 and R == 0: probs.append((el, 'zero target')); continue
        if rB == 0:
            # P*3^(k-m) + R: zero digit if k - m > len(R) (digits of R below, of P above, a gap between)
            if P == 0: probs.append((el, 'constant target')); continue
            Kstar = max(Kstar, m + bt_len(R) + 1)
        else:
            Q, mq = split_power(rB)                    # coefficient of Y = 3^i, i.e. Q*3^(i - mq)
            # generic i in [L, k-U]: need i - mq > len(R) and k - m > i - mq + len(Q)
            need_low = L - mq > bt_len(R)
            need_high = U + m - mq - bt_len(Q) >= 1    # k - m - (k - U - mq + len Q) >= 1
            if not (need_low and need_high): probs.append((el, 'gap', L, U, m, mq, bt_len(Q), bt_len(R)))
            Kstar = max(Kstar, L + U + m + 1)
    return (not probs), Kstar, probs

def certificate(a, b):
    from prover import fit
    from reach import is_member
    lines = []; ok = True; Kall = 0
    for par, (k1, k2) in ((0, (12, 14)), (1, (13, 15))):
        hyp = fit(a, b, k1, k2)
        if hyp is None: return False, [f"parity {par}: no hypothesis"], None
        f = closure_all_k(a, b, hyp, par)
        na, Kstar, pr = nonaccept_all_k(a, b, hyp, par)
        L, U = bounds(hyp)
        Kstar = max(Kstar, L + U + 2, k2)
        Kall = max(Kall, Kstar)
        lines.append(f"parity {par}: closure {'PASS' if not f else 'FAIL'}; non-acceptance {'PASS' if na else 'FAIL ' + str(pr[:2])}; symbolic for k >= {Kstar}")
        ok &= (not f) and na
    # exhaustive exact check below Kall, from the first k where the family is a non-member onwards
    ks = ['M' if is_member(a*3**k + b) else 'x' for k in range(1, Kall + 1)]
    first = Kall
    while first > 1 and ks[first - 2] == 'x': first -= 1       # smallest k with x from k to Kall
    if ks[Kall - 1] != 'x': ok = False
    lines.append(f"exact search k=1..{Kall}: {''.join(ks)}  -> non-member for all k >= {first}")
    return ok, lines, first

if __name__ == "__main__" and len(sys.argv) > 3 and sys.argv[3] == "cert":
    a, b = int(sys.argv[1]), int(sys.argv[2])
    ok, lines, first = certificate(a, b)
    for l in lines: print(" ", l)
    print(f"THEOREM {'PROVED' if ok else 'NOT PROVED'}: {a}*3^k + {b} is not in B/B for all k >= {first}")
