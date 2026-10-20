"""First-order event exploration for the delayed-pentagon conjecture.

Coordinates and coefficients are exact elements of Q(sqrt(3),sqrt(19)).
Sign comparisons and coordinate orderings use rational ordered-field arithmetic.
The six inputs are the first-order (3,2) threshold fronts with inherited lineage
bearing offsets. The event tree branches over height ties, reporting 34 leaves.

LIMITATION: zero constant and linear clearance coefficients do not establish
validity. Treating such a candidate as valid can hide a higher candidate if a
quadratic term excludes the lower one. The exact-threshold triangle rule also
needs a separate nonlinear perturbation argument. This is an exploration, not
a certificate for all small mismatch/rate pairs. AUDIT counts unresolved
nonparent clearances among selected candidates; it is not a full validity tree.
Numerical evaluation remains available only for diagnostics, not decisions.
"""

from __future__ import annotations

from fractions import Fraction as Fr
from functools import cmp_to_key

from mpmath import mp, mpf
from mpmath import sqrt as msqrt

mp.dps = 60
S3, S19 = msqrt(3), msqrt(19)


class K:
    """a + b sqrt3 + c sqrt19 + d sqrt57, exact rationals."""

    __slots__ = ("v",)

    def __init__(self, a=0, b=0, c=0, d=0):
        self.v = (Fr(a), Fr(b), Fr(c), Fr(d))

    def __add__(self, o):
        o = o if isinstance(o, K) else K(o)
        return K(*(x + y for x, y in zip(self.v, o.v)))

    __radd__ = __add__

    def __neg__(self):
        return K(*(-x for x in self.v))

    def __sub__(self, o):
        return self + (-(o if isinstance(o, K) else K(o)))

    def __rsub__(self, o):
        return K(o) - self

    def __mul__(self, o):
        if not isinstance(o, K):
            o = K(o)
        a, b, c, d = self.v
        e, f, g, h = o.v
        # basis 1, r3, r19, r57: r3 r3 = 3, r3 r19 = r57, r3 r57 = 3 r19, r19 r19 = 19, r19 r57 = 19 r3, r57 r57 = 57
        return K(
            a * e + 3 * b * f + 19 * c * g + 57 * d * h,
            a * f + b * e + 19 * c * h + 19 * d * g,
            a * g + c * e + 3 * b * h + 3 * d * f,
            a * h + d * e + b * g + c * f,
        )

    __rmul__ = __mul__

    def conj3(self):
        a, b, c, d = self.v
        return K(a, -b, c, -d)

    def conj19(self):
        a, b, c, d = self.v
        return K(a, b, -c, -d)

    def inv(self):
        p = self.conj3() * self.conj19() * self.conj3().conj19()
        n = self * p
        assert n.v[1] == n.v[2] == n.v[3] == 0, "norm not rational"
        return p * K(1 / n.v[0])

    def __truediv__(self, o):
        return self * (o if isinstance(o, K) else K(o)).inv()

    def iszero(self):
        return all(x == 0 for x in self.v)

    def num(self):
        a, b, c, d = self.v
        return (
            mpf(a.numerator) / a.denominator
            + mpf(b.numerator) / b.denominator * S3
            + mpf(c.numerator) / c.denominator * S19
            + mpf(d.numerator) / d.denominator * S3 * S19
        )

    def sign(self):
        """Exact ordered-field comparison; no floating-point sign oracle.

        Write the value as x + y*sqrt(19), x,y in Q(sqrt(3)).
        If the summands have opposite signs, compare x*x with 19*y*y.
        """
        if self.iszero():
            return 0
        a, b, c, d = self.v

        def quadratic_sign(r, s):
            sr = (r > 0) - (r < 0)
            ss = (s > 0) - (s < 0)
            if sr == 0:
                return ss
            if ss == 0 or sr == ss:
                return sr
            norm = r*r - 3*s*s
            assert norm != 0  # sqrt(3) is irrational
            return sr if norm > 0 else ss

        sx, sy = quadratic_sign(a, b), quadratic_sign(c, d)
        if sx == 0:
            return sy
        if sy == 0 or sx == sy:
            return sx
        norm_sign = quadratic_sign(a*a + 3*b*b - 19*c*c - 57*d*d,
                                   2*a*b - 38*c*d)
        assert norm_sign != 0  # sqrt(19) is not in Q(sqrt(3))
        return sx if norm_sign > 0 else sy


R3, R19, R57 = K(0, 1), K(0, 0, 1), K(0, 0, 0, 1)
ZERO = K()
AUDIT = {"selected_unresolved_clearances": 0, "steps": 0}


def sgn2(p):
    """Sign of a first-order quantity (x0, x1): x0 decides, else x1."""
    s = p[0].sign()
    return s if s != 0 else p[1].sign()


def model(X, Y):
    """Rational-model point (X, Y) -> real coordinates (X/sqrt19, sqrt3 Y/sqrt19)."""
    return (K(Fr(X)) * R19 * K(Fr(1, 19)), K(Fr(Y)) * R57 * K(Fr(1, 19)))


# ---- the threshold lattice and its first-order deformation ----
D0 = model(4, -1)  # down vector
U0 = model(Fr(7, 2), Fr(3, 2))  # up vector (D rotated by +60)
OFF = {
    "Ua/+": Fr(1, 2),
    "Ua/-": Fr(1, 2),
    "Ub/+": Fr(-1, 2),
    "Ub/-": Fr(-1, 2),
    "D": Fr(-1, 2),
}


def front(word):
    """Disks (x0, x1), (y0, y1) of the threshold front of `word`, and the circumference (L0, L1)."""
    ups = [w for w in word if w.endswith("/+")]
    downs = [w for w in word if not w.endswith("/+")]
    # threshold: max over notches (down then up) of off_D - off_U equals u1 - d1
    N = len(word)
    notch = [
        OFF[word[k]] - OFF[word[(k + 1) % N]]
        for k in range(N)
        if not word[k].endswith("/+") and word[(k + 1) % N].endswith("/+")
    ]
    delta = max(notch)  # u1 - d1
    # closure: sum over ups cos u0 (u1 + off) + sum over downs cos d0 (d1 + off) = 0, cos u0 = 3.5/sqrt19, cos d0 = 4/sqrt19
    cu, cd = Fr(7, 2), Fr(4)
    # u1 = d1 + delta
    d1 = -(
        cu * (len(ups) * delta + sum(OFF[w] for w in ups))
        + cd * sum(OFF[w] for w in downs)
    ) / (cu * len(ups) + cd * len(downs))
    u1 = d1 + delta
    vecs = []
    for w in word:
        v0 = U0 if w.endswith("/+") else D0
        th1 = (u1 if w.endswith("/+") else d1) + OFF[w]
        v1 = (-v0[1] * K(th1), v0[0] * K(th1))  # i v0 th1
        vecs.append((v0, v1))
    pts = [((ZERO, ZERO), (ZERO, ZERO))]
    for v0, v1 in vecs[:-1]:
        (x0, y0), (x1, y1) = pts[-1]
        pts.append(((x0 + v0[0], y0 + v0[1]), (x1 + v1[0], y1 + v1[1])))
    L0 = sum((v[0][0] for v in vecs), ZERO)
    L1 = sum((v[1][0] for v in vecs), ZERO)
    assert (
        sum((v[0][1] for v in vecs), ZERO).iszero()
        and sum((v[1][1] for v in vecs), ZERO).iszero()
    )
    return pts, (L0, L1), [w for w in word]


def shift(p, s, L):
    (x0, y0), (x1, y1) = p
    return ((x0 + K(s) * L[0], y0), (x1 + K(s) * L[1], y1))


def d2(p, q):
    """|q - p|^2 to first order."""
    (px0, py0), (px1, py1) = p
    (qx0, qy0), (qx1, qy1) = q
    dx0, dy0, dx1, dy1 = qx0 - px0, qy0 - py0, qx1 - px1, qy1 - py1
    return (dx0 * dx0 + dy0 * dy0, K(2) * (dx0 * dx1 + dy0 * dy1))


def apex(p, r):
    """Unit-distance apex above p -> r, to first order; None if absent; 'DEG' if |p0 r0| = 2."""
    D2 = d2(p, r)
    s = (D2[0] - K(4)).sign()
    if s > 0:
        return None
    if s == 0:
        return "DEG"
    (px0, py0), (px1, py1) = p
    (rx0, ry0), (rx1, ry1) = r
    # zeroth order: midpoint + J(r - p) * sqrt(1/|r-p|^2 - 1/4); in a triangular lattice |r-p|^2 in {1, 3}
    L2 = D2[0]
    if (L2 - K(1)).iszero():
        h = K(1, 0) * R3 * K(Fr(1, 2))  # sqrt(3)/2
    elif (L2 - K(3)).iszero():
        h = R3 * K(Fr(1, 6)) * K(1)  # sqrt(1/3 - 1/4) = 1/(2 sqrt3) = sqrt3/6
    else:
        raise ValueError("apex of a non-lattice pair")
    dx, dy = rx0 - px0, ry0 - py0
    qx0 = (px0 + rx0) * K(Fr(1, 2)) - h * dy
    qy0 = (py0 + ry0) * K(Fr(1, 2)) + h * dx
    # first order: (q0 - p0).(q1 - p1) = 0, (q0 - r0).(q1 - r1) = 0
    a1, b1 = qx0 - px0, qy0 - py0
    a2, b2 = qx0 - rx0, qy0 - ry0
    c1 = a1 * px1 + b1 * py1
    c2 = a2 * rx1 + b2 * ry1
    det = a1 * b2 - a2 * b1
    qx1 = (c1 * b2 - c2 * b1) / det
    qy1 = (a1 * c2 - a2 * c1) / det
    return ((qx0, qy0), (qx1, qy1))


def step(state):
    """All lowest valid placements (ties branch). state = (disks, front, labels, L)."""
    disks, F, labels, L = state
    AUDIT["steps"] += 1
    N = len(F)
    cands = []
    for a in range(N):
        for gap in range(N - 1):
            b = (a + gap + 1) % N
            P = disks[F[a]]
            R = disks[F[b]] if b > a else shift(disks[F[b]], 1, L)
            if sgn2((R[0][0] - P[0][0], R[1][0] - P[1][0])) <= 0:
                continue
            Q = apex(P, R)
            if Q is None:
                continue
            if Q == "DEG":
                cands.append(("DEG", a, gap))
                continue
            ok = True
            for k, z in enumerate(disks):
                for s in (-1, 0, 1):
                    if (k == F[a] and s == 0) or (
                        k == F[b] and s == (0 if b > a else 1)
                    ):
                        continue
                    cl = d2(shift(z, s, L), Q)
                    if sgn2((cl[0] - K(1), cl[1])) < 0:
                        ok = False
                        break
                if not ok:
                    break
            if ok:
                cands.append((Q, a, gap))
    real = [c for c in cands if c[0] != "DEG"]
    def compare_height(a, b):
        return sgn2((a[0][0][1] - b[0][0][1], a[0][1][1] - b[0][1][1]))
    best = min(real, key=cmp_to_key(compare_height))
    ties = [
        c
        for c in real
        if (c[0][0][1] - best[0][0][1]).iszero()
        and (c[0][1][1] - best[0][1][1]).iszero()
    ]
    # These are exploratory branches: a zero jet is not a validity certificate.
    for Q, a, gap in ties:
        b = (a + gap + 1) % N
        for k, z in enumerate(disks):
            for sh in (-1, 0, 1):
                if (k == F[a] and sh == 0) or (k == F[b] and sh == (0 if b > a else 1)):
                    continue
                clearance = d2(shift(z, sh, L), Q)
                if (clearance[0] - K(1)).iszero() and clearance[1].iszero():
                    AUDIT["selected_unresolved_clearances"] += 1
    degs = []
    for c in cands:
        if c[0] != "DEG":
            continue
        _, a, gap = c
        b = (a + gap + 1) % N
        P = disks[F[a]]
        R = disks[F[b]] if b > a else shift(disks[F[b]], 1, L)
        mx, my = (P[0][0] + R[0][0]) * K(Fr(1, 2)), (P[0][1] + R[0][1]) * K(Fr(1, 2))
        if (my - best[0][0][1]).sign() > 0:
            continue  # higher than the chosen position at zeroth order
        blocked = False
        for k, z in enumerate(disks):
            for sh in (-1, 0, 1):
                zx, zy = z[0][0] + K(sh) * L[0], z[0][1]
                if ((zx - mx) * (zx - mx) + (zy - my) * (zy - my) - K(1)).sign() < 0:
                    blocked = True
        if not blocked:
            degs.append(c)
    return ties, degs


def place(state, cand):
    disks, F, labels, L = state
    Q, a, gap = cand
    N = len(F)
    if sgn2((Q[0][0] - L[0], Q[1][0] - L[1])) >= 0:
        Q = shift(Q, -1, L)
    elif sgn2((Q[0][0], Q[1][0])) < 0:
        Q = shift(Q, 1, L)
    disks = disks + [Q]
    q = len(disks) - 1
    rot = F[a:] + F[:a]
    lab = labels[a:] + labels[:a]
    if gap == 0:
        newF, newL = [rot[0], q] + rot[1:], [lab[0] + "/+", lab[0] + "/-"] + lab[1:]
    elif gap == 1:
        newF, newL = [rot[0], q] + rot[2:], [lab[1], lab[0]] + lab[2:]
    else:
        newF = [rot[0], q] + rot[gap + 1 :]
        newL = ["P(" + ",".join(lab[: gap + 1]) + ")/+", "P/-"] + lab[gap + 1 :]
    # wrap x into [0, L) at zeroth order is not needed: sort cyclically by x relative to rot[0]

    def compare_x(a, b):
        (x0, _), (x1, _) = disks[a[0]]
        (y0, _), (y1, _) = disks[b[0]]
        return sgn2((x0-y0, x1-y1))

    pairs = sorted(zip(newF, newL), key=cmp_to_key(compare_x))
    return (disks, [p[0] for p in pairs], [p[1] for p in pairs], L)


def parastichy(state):
    disks, F, _, L = state
    downs = 0
    for k in range(len(F)):
        p = disks[F[k]]
        q = disks[F[(k + 1) % len(F)]] if k + 1 < len(F) else shift(disks[F[0]], 1, L)
        if sgn2((q[0][1] - p[0][1], q[1][1] - p[1][1])) < 0:
            downs += 1
    return downs, len(F) - downs


def exact_threshold(labels, a, orig, delta):
    """The notch (labels[a], labels[a+1]) is made of two original front vectors whose hinge is exactly
    120 deg + eta at every order (offset difference = delta), so by [GD] its offspring is the triangle."""
    N = len(labels)
    d, u = labels[a], labels[(a + 1) % N]
    return d in orig and u in orig and not d.endswith("/+") and u.endswith("/+") and OFF[d] - OFF[u] == delta


def explore(state, path, out, orig, delta, depth=0):
    if depth > 7:
        out.append((path, "TOO LONG"))
        return
    ties, degs = step(state)
    ties = [c for c in ties if not (c[2] == 1 and exact_threshold(state[2], c[1], orig, delta))]
    for dg in degs:
        out.append((path, f"DEGENERATE apex at pair {dg[1]}+{dg[2]} (check height)"))
    tag = " (tie)" if len(ties) > 1 else ""
    for c in ties:
        ev = "TRP"[c[2]] if c[2] < 3 else f"G{c[2]}"
        new = place(state, c)
        p = parastichy(new)
        step_path = path + [f"{ev}{p}{tag}"]
        if c[2] >= 2:
            out.append((step_path, "PENTAGON" if c[2] == 2 else f"GAP {c[2]}"))
        else:
            explore(new, step_path, out, orig, delta, depth + 1)


if __name__ == "__main__":
    cycle = [
        "Ua/+ Ua/- Ub/+ D Ub/-",
        "Ua/+ Ub/- Ua/- Ub/+ D",
        "Ua/+ Ub/- Ub/+ Ua/- D",
        "Ua/+ D Ub/- Ub/+ Ua/-",
        "Ua/+ D Ub/+ Ub/- Ua/-",
        "Ua/+ Ua/- D Ub/+ Ub/-",
    ]
    allok = True
    for w in cycle:
        pts, L, labels = front(w.split())
        F = list(range(len(pts)))
        state = (pts, F, labels, L)
        out = []
        ws = w.split()
        notch = [OFF[ws[k]] - OFF[ws[(k + 1) % len(ws)]] for k in range(len(ws))
                 if not ws[k].endswith("/+") and ws[(k + 1) % len(ws)].endswith("/+")]
        explore(state, [], out, set(ws), max(notch))
        print(f"[{w}]  parastichy {parastichy(state)}")
        for path, res in out:
            print("   ", " -> ".join(path), "=>", res)
            if res != "PENTAGON" or any("(8, 5)" in s or "(5, 8)" in s for s in path):
                allok = False
    print("every represented branch ends in a pentagon before (8,5):", allok)
    print("Exploratory computation; unresolved validity jets:", AUDIT)
    print("A nonlinear certificate must also branch over undecided validity and threshold rules.")
    assert allok
