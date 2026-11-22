"""Exact decision: does {q in E^(n-1) : A q = 0} contain a point with all q_j nonzero and pairwise distinct?

Smith form A = U D V (U, V unimodular). Put w = V q; then D w = 0: w_l in E[d_l] for d_l != 0 (l < rank),
w_l free for l >= rank (columns with no pivot). q = V^-1 w. Write q_j = F_j(w_free) + T_j(w_tors).
For generic w_free, F_j(w_free) = F_k(w_free) iff the free rows agree, and F_j(w_free) = 0 iff the free row is 0.
So a distinct nonzero solution exists iff some torsion choice t in prod E[d_l] = prod (Z/d_l)^2 makes
T_j(t) != 0 whenever F_j = 0, and T_j(t) != T_k(t) whenever F_j = F_k.
"""
import itertools

import sympy as S
from sympy.matrices.normalforms import smith_normal_form


def smith_decomp(A):
    """Return (D, V) with U A V^-1 ... computed by sympy's invariant factors plus an explicit V via Hermite steps."""
    M = S.Matrix(A)
    # use a simple column-reduction to get unimodular V with A V^-1 lower-triangular is complicated; instead use
    # sympy's smith_normal_decomp if available.
    from sympy.matrices.normalforms import smith_normal_decomp
    D, U, Vm = smith_normal_decomp(M, domain=S.ZZ)   # D = U * M * Vm
    return D, U, Vm


def decide(A, n):
    if n <= 1:
        return "none"
    if not A:
        A = [[0] * (n - 1)]
    M = S.Matrix(A)
    D, U, Vm = smith_decomp(A)
    # D = U M Vm, so M q = 0 <=> D (Vm^-1 q) = 0. Let w = Vm^-1 q, q = Vm w.
    r = sum(1 for k in range(min(D.shape)) if D[k, k] != 0)
    dvals = [abs(int(D[k, k])) for k in range(r)]
    ncols = n - 1
    free = list(range(r, ncols))
    tors = [k for k in range(r) if dvals[k] > 1]
    Fj = [tuple(Vm[j, l] for l in free) for j in range(ncols)]
    choices = [list(itertools.product(range(dvals[k]), repeat=2)) for k in tors]
    for t in itertools.product(*choices) if tors else [()]:
        T = []
        for j in range(ncols):
            # T_j = sum_k Vm[j, k] * t_k in E[lcm]; represent in Q/Z coordinates
            v = [S.Rational(0), S.Rational(0)]
            for k, tk in zip(tors, t):
                v[0] += Vm[j, k] * S.Rational(tk[0], dvals[k])
                v[1] += Vm[j, k] * S.Rational(tk[1], dvals[k])
            T.append(tuple(x - S.floor(x) for x in v))
        ok = True
        for j in range(ncols):
            if all(c == 0 for c in Fj[j]) and T[j] == (0, 0):
                ok = False
                break
        if ok:
            for j, k in itertools.combinations(range(ncols), 2):
                if Fj[j] == Fj[k] and T[j] == T[k]:
                    ok = False
                    break
        if ok:
            kind = f"family d={len(free)}" if free else "torsion"
            return kind + (f" N={max(dvals)}" if tors else "")
    return "none"
