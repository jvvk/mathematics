"""Rigorous version of certify_simplex.py (depth-(DS,DT) lookahead), with exact rational (a, c).

The subdivision search is the same as certify_simplex.py and runs in float64. A sub-simplex is ACCEPTED only
after a rigorous check of the certificate found for it:

* Vertices are dyadic. They are scaled by 2^52 to exact integers (asserted), so every linear form
  L.y at a vertex is an exact integer over 2^52.
* Lower bounds for x^a (a = p/q exact) are floats r with r^q <= x^p checked in exact integer arithmetic;
  lower bounds for the weights 2^(c*ds) likewise (r^den <= 2^(num*ds)).
* A strategy value is a sum of at most TERMS products; its float lower bound is computed from these
  lower bounds and must be >= 1 + SLACK, where SLACK exceeds the worst-case float rounding of those
  few operations (each relative error <= 2^-53), so the true value is >= 1 at every vertex.
* An LP combination sum_j lam_j phi_j is accepted only if sum lam_j <= 1 holds exactly (Fractions),
  lam_j >= 0, and its rigorous lower bound is >= 1 + SLACK at every vertex. Since every phi_j is concave
  and nonnegative, sum lam_j phi_j is concave and <= max_j phi_j, so it certifies the simplex.

Usage: certify_simplex_rig.py DS,DT a c [maxsimplices]      with a, c as exact rationals, e.g. 2/5 157/2000
"""

from __future__ import annotations

import math
import sys
import time
from fractions import Fraction

import numpy as np
from scipy.optimize import linprog

from strategies import build

DS, DT = map(int, sys.argv[1].split(","))
A, C = Fraction(sys.argv[2]), Fraction(sys.argv[3])
CAP = int(sys.argv[4]) if len(sys.argv) > 4 else 50_000_000
a, c = float(A), float(C)
mS, mT = 1 << DS, 1 << DT
dim = mS * mT
MARGIN = 1e-9  # search heuristic only
SLACK = (
    2.0**-40
)  # rigorous acceptance threshold above 1 (covers float rounding, see docstring)
SCALE = 1 << 52


def leaves(u, Dd):
    k = Dd - len(u)
    base = (int("".join(map(str, u)), 2) << k) if u else 0
    return range(base, base + (1 << k))


strats = build(DS, DT)
forms, wts = [], []
fidx: dict = {}
for j, s in enumerate(strats):
    for ds, u, v in s:
        if (u, v) not in fidx:
            vec = np.zeros(dim, dtype=np.int64)
            for p in leaves(u, DS):
                for q in leaves(v, DT):
                    vec[p * mT + q] = 1
            fidx[(u, v)] = len(forms)
            forms.append(vec)
        wts.append((fidx[(u, v)], ds, j))
Fi = np.array(forms)  # integer 0/1 form matrix
Ff = Fi.astype(float)
T_form = np.array([w[0] for w in wts])
T_ds = np.array([w[1] for w in wts])
T_s = np.array([w[2] for w in wts])
NS = len(strats)
S = np.zeros((NS, len(wts)))
S[T_s, np.arange(len(wts))] = 2.0 ** (c * T_ds)
TERMS = max(len(s) for s in strats)
by_strat = [[(fidx[(u, v)], ds) for (ds, u, v) in s] for s in strats]


# ---------- rigorous lower bounds ----------
def lo_weight(ds: int) -> float:
    """Float r <= 2^(C*ds), checked as r^den <= 2^(num*ds) exactly."""
    r = 2.0 ** (c * ds) * (1 - 2.0**-45)
    num, den = (C * ds).numerator, (C * ds).denominator
    while True:
        n, d = r.as_integer_ratio()
        if n**den <= d**den * 2**num:
            return r
        r = math.nextafter(r, 0.0)


W_LO = {ds: lo_weight(int(ds)) for ds in set(T_ds.tolist())}
P_CACHE: dict[int, float] = {}
p_, q_ = A.numerator, A.denominator


def lo_pow(xi: int) -> float:
    """Float r <= (xi / 2^52)^(p/q), checked as r^q * 2^(52 p) <= xi^p * ... exactly."""
    if xi == 0:
        return 0.0
    r = P_CACHE.get(xi)
    if r is not None:
        return r
    r = (xi / SCALE) ** a * (1 - 2.0**-45)
    while True:
        n, d = r.as_integer_ratio()
        # r^q <= (xi/2^52)^p   <=>   n^q * 2^(52p) <= xi^p * d^q
        if n**q_ * (1 << (52 * p_)) <= xi**p_ * d**q_:
            P_CACHE[xi] = r
            return r
        r = math.nextafter(r, 0.0)


def rig_strategy(j: int, Li: np.ndarray) -> float:
    """Rigorous-ish float lower bound of strategy j at every vertex (min over vertices); caller adds SLACK."""
    worst = math.inf
    for k in range(Li.shape[1]):
        tot = 0.0
        for f, ds in by_strat[j]:
            tot += W_LO[ds] * lo_pow(int(Li[f, k]))
        worst = min(worst, tot)
    return worst


def int_vertices(V: np.ndarray) -> np.ndarray:
    Vs = V * SCALE
    assert np.all(np.floor(Vs) == Vs) and np.all(Vs >= 0), (
        "vertex not dyadic within 2^-52"
    )
    return Vs.astype(np.int64)


def values(V):
    L = np.clip(Ff @ V.T, 0, None)
    return S @ np.power(L, a)[T_form]


# ---------- search ----------
t0 = time.time()
stack, depths = [np.eye(dim)], [0]
done = nlp = rig_fail = 0
maxdepth = 0
worst_vertex = math.inf
while stack:
    V = stack.pop()
    d = depths.pop()
    maxdepth = max(maxdepth, d)
    with np.errstate(all="ignore"):
        val = values(V)
    if not np.isfinite(val).all():
        print("NONFINITE value: abort")
        sys.exit(4)
    vmax = val.max(0)
    worst_vertex = min(worst_vertex, float(vmax.min()))
    if vmax.min() < 1 - 1e-6:
        print(f"COUNTEREXAMPLE (float): vertex max phi = {vmax.min():.6f}")
        print(np.round(V[int(vmax.argmin())].reshape(mS, mT), 4))
        sys.exit(1)
    ok = False
    good = np.nonzero(val.min(1) >= 1 + MARGIN)[0]
    if len(good):
        Li = Fi @ int_vertices(V).T
        j = int(good[np.argmax(val.min(1)[good])])
        ok = rig_strategy(j, Li) >= 1 + SLACK
        rig_fail += not ok
    if not ok:
        cand = np.unique(np.argsort(-val, axis=0)[:6].ravel())
        Am = val[cand]
        nc, k = Am.shape
        res = linprog(
            np.r_[np.zeros(nc), -1.0],
            A_ub=np.c_[-Am.T, np.ones(k)],
            b_ub=np.zeros(k),
            A_eq=np.r_[np.ones(nc), 0.0][None],
            b_eq=[1.0],
            bounds=[(0, None)] * nc + [(None, None)],
            method="highs",
        )
        if res.status == 0 and -res.fun >= 1 + 1e-6:
            lam = np.clip(res.x[:nc], 0, None)
            lam = lam / lam.sum() * (1 - 2.0**-40)
            if sum(Fraction(float(x)) for x in lam) <= 1:  # exact
                Li = Fi @ int_vertices(V).T
                worst = math.inf
                for kk in range(Li.shape[1]):
                    tot = 0.0
                    for lj, j in zip(lam, cand):
                        if lj > 0:
                            for f, ds in by_strat[int(j)]:
                                tot += float(lj) * (W_LO[ds] * lo_pow(int(Li[f, kk])))
                    worst = min(worst, tot)
                ok = worst >= 1 + SLACK
                nlp += ok
    if ok:
        done += 1
        if done % 200000 == 0:
            print(
                f"  certified {done} (LP {nlp}), stack {len(stack)}, depth {maxdepth}, "
                f"cache {len(P_CACHE)}, {time.time() - t0:.0f}s",
                flush=True,
            )
        if done > CAP:
            print(
                f"CAP reached: {done} certified in {time.time() - t0:.0f}s, stack {len(stack)}"
            )
            sys.exit(2)
        continue
    if d > 400:
        print("DEPTH LIMIT")
        sys.exit(3)
    G = V @ V.T
    nrm = np.diag(G)
    E = nrm[:, None] + nrm[None, :] - 2 * G
    p, q = np.unravel_index(int(E.argmax()), E.shape)
    mid = (V[p] + V[q]) / 2
    V1 = V.copy()
    V1[p] = mid
    V2 = V.copy()
    V2[q] = mid
    stack += [V1, V2]
    depths += [d + 1, d + 1]
print(
    f"CERTIFIED (rigorous) DS={DS} DT={DT} a={A} c={C} exponent a-2c={A - 2 * C} = {float(A - 2 * C)}: "
    f"{done} simplices, max depth {maxdepth}, LP {nlp}, float-accepted but rigor-rejected {rig_fail}, "
    f"min vertex max-phi {worst_vertex:.6f}, distinct powers {len(P_CACHE)}, {time.time() - t0:.1f}s"
)
