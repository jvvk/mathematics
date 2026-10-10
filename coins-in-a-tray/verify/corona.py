"""Closed coronas (MO 513668). Around a coin of curvature m, a closed corona is a cyclic sequence of neighbours
(coins of curvature 2..n, or the tray T = curvature -1, at most once), consecutive neighbours tangent to each other,
all tangent to the centre coin, no two neighbours overlapping, contact directions turning by exactly 2 pi.
If the contact graph of a packing (tray included) is a triangulation, every coin has a closed corona.

Angle between contact directions to neighbours a, b of coin m: the triangle of centres has sides
|1/m+1/a|, |1/m+1/b|, |1/a+1/b| (signed curvature -1 for the tray), so cos is rational; if exactly one neighbour is
the tray the contact direction is reversed, cos -> -cos. e^{i theta} lies in Q(i, sqrt(q^2-p^2)) for cos = p/q, so
the Galois argument applies verbatim: class = squarefree part of q^2 - p^2, class sums are multiples of pi/12.
Stages as in rim_exact.py: per class bounded enumeration (80-digit rationality test), combine to 2 pi, realise as
an Euler circuit on neighbour types, check overlaps, verify at 300 digits.
Usage: corona.py n [m ...]   (default: every m in 2..n)
The exact search is corona_certify.py, which imports the helpers below; this numerical search is kept as an
independent cross-check of it."""

import itertools
import math
import sys
from collections import Counter, defaultdict
from fractions import Fraction

from mpmath import acos, mp, mpf, pi

mp.dps = 80
T = -1
TRUNC = []


def sqf(m):
    a, p = 1, 2
    while p * p <= m:
        while m % (p * p) == 0:
            m //= p * p
        if m % p == 0:
            a *= p
            m //= p
        p += 1
    return a * m


def inv(x):
    return Fraction(-1) if x == T else Fraction(1, x)


def cos_angle(m, a, b):
    dma, dmb, dab = (
        abs(Fraction(1, m) + inv(a)),
        abs(Fraction(1, m) + inv(b)),
        abs(inv(a) + inv(b)),
    )
    c = (dma**2 + dmb**2 - dab**2) / (2 * dma * dmb)
    return -c if (a == T) != (b == T) else c


def angle_types(m, n):
    nb = [T] + list(range(2, n + 1))
    out = {}
    for a, b in itertools.combinations_with_replacement(nb, 2):
        if a == T and b == T:
            continue
        c = cos_angle(m, a, b)
        if not (-1 < c < 1):
            continue  # degenerate (angle 0 or pi) handled as rational below if c == -1
        out[(a, b)] = c
    # c == -1 (angle pi) is possible, e.g. m=2 with T and 2: include it
    for a, b in itertools.combinations_with_replacement(nb, 2):
        if a == T and b == T:
            continue
        if cos_angle(m, a, b) == -1:
            out[(a, b)] = Fraction(-1)
    return out


def theta(c):
    return acos(mpf(c.numerator) / c.denominator)


def cls_key(c):
    if c in (0, Fraction(1, 2), Fraction(-1, 2), 1, -1):
        return 0  # rational angles (Niven)
    return sqf(c.denominator**2 - c.numerator**2)


def rational_pi(x):
    t = x / pi
    for q in (1, 2, 3, 4, 6, 12):
        p = mp.nint(t * q)
        if abs(t * q - p) < mpf(10) ** -60:
            return Fraction(int(p), q)
    return None


def coronas(m, n, cap=300000):
    at = angle_types(m, n)
    groups = defaultdict(list)
    for pr, c in at.items():
        groups[cls_key(c)].append(pr)
    # stage 1 per class
    opts = {}
    for key, prs in groups.items():
        ths = [theta(at[p]) for p in prs]
        caps = [int(2 * pi / t + 1e-9) if t > 0 else 0 for t in ths]
        res = []

        def rec(i, acc, vec):
            if acc > 2 * pi + mpf(10) ** -50:
                return
            if i == len(prs):
                if any(vec):
                    r = rational_pi(acc)
                    if r is not None:
                        res.append((tuple(vec), r))
                return
            for k in range(caps[i] + 1):
                if acc + k * ths[i] > 2 * pi + mpf(10) ** -50:
                    break
                vec.append(k)
                rec(i + 1, acc + k * ths[i], vec)
                vec.pop()

        rec(0, mpf(0), [])
        if res:
            opts[key] = (prs, res)
    # stage 2
    keys = list(opts)
    combos = []

    def rec2(i, tot, chosen):
        if tot > 2:
            return
        if i == len(keys):
            if tot == 2:
                combos.append(list(chosen))
            return
        rec2(i + 1, tot, chosen)
        prs, res = opts[keys[i]]
        for vec, r in res:
            chosen.append((prs, vec))
            rec2(i + 1, tot + r, chosen)
            chosen.pop()

    rec2(0, Fraction(0), [])
    # stage 3: Euler circuits on neighbour types, overlap check
    sols = set()
    for combo in combos:
        edges = []
        for prs, vec in combo:
            for p, k in zip(prs, vec):
                edges += [p] * k
        deg = Counter()
        for a, b in edges:
            deg[a] += 1
            deg[b] += 1
        if any(v % 2 for v in deg.values()):
            continue
        if deg[T] > 2:
            continue  # tray at most once in the corona
        for s in circuits(m, edges, at, cap):
            k = len(s)
            reps = [tuple(s[i:] + s[:i]) for i in range(k)] + [
                tuple(s[::-1][i:] + s[::-1][:i]) for i in range(k)
            ]
            sols.add(min(reps))
    return sols, len(combos)


def circuits(m, edges, at, cap):
    adj = Counter((min(a, b), max(a, b)) for a, b in edges)
    E = len(edges)
    start = T if any(T in e for e in adj) else min(x for e in adj for x in e)
    seq, ang = [start], [0.0]
    rm = 1 / m

    def centre(x, th):
        if (
            x == T
        ):  # tray centre: opposite to the contact direction, at distance 1 - 1/m
            return (-(1 - rm) * math.cos(th), -(1 - rm) * math.sin(th))
        d = rm + 1 / x
        return (d * math.cos(th), d * math.sin(th))

    def ok(x, th):
        cx = centre(x, th)
        for y, t in zip(seq[:-1], ang[:-1]):
            if len(seq) == E and y == seq[0]:
                continue
            cy = centre(y, t)
            dist = math.hypot(cx[0] - cy[0], cx[1] - cy[1])
            if x == T or y == T:
                r = 1 / (y if x == T else x)
                if dist > 1 - r + 1e-9:
                    return False  # coin must stay inside the tray
            elif dist < 1 / x + 1 / y - 1e-9:
                return False
        return True

    def fits(sq, an):
        # necessary condition when the tray is not in the corona: every two disks of the cluster (centre coin
        # included) fit inside a diameter, dist + r1 + r2 <= 2
        if T in sq: return True
        disks = [((0.0, 0.0), rm)] + [(centre(x, t), 1 / x) for x, t in zip(sq, an)]
        for (p, r1), (q, r2) in itertools.combinations(disks, 2):
            if math.hypot(p[0] - q[0], p[1] - q[1]) + r1 + r2 > 2 + 1e-9: return False
        return True
    count = [0]

    def rec():
        if count[0] > cap:
            TRUNC.append(m)
            return
        if len(seq) == E + 1:
            if seq[-1] == seq[0] and fits(seq[:-1], ang[:-1]):
                count[0] += 1
                yield list(seq[:-1])
            return
        a = seq[-1]
        for e in list(adj):
            if adj[e] == 0 or a not in e:
                continue
            b = e[1] if e[0] == a else e[0]
            if b == T and T in seq[1:]:
                continue
            th = ang[-1] + float(acos(mpf(at[e].numerator) / at[e].denominator))
            if len(seq) < E and not ok(b, th):
                continue
            adj[e] -= 1
            seq.append(b)
            ang.append(th)
            yield from rec()
            adj[e] += 1
            seq.pop()
            ang.pop()

    yield from rec()


if __name__ == "__main__":
    n = int(sys.argv[1])
    ms = [int(x) for x in sys.argv[2:]] or list(range(2, n + 1))
    for m in ms:
        sols, nc = coronas(m, n)
        lab = lambda s: tuple("T" if x == T else x for x in s)
        print(
            f"n={n} coin 1/{m}: exact-2pi multisets {nc}, closed coronas {len(sols)}  truncated={m in TRUNC}",
            flush=True,
        )
        for s in sorted(sols, key=len)[:6]:
            print("     ", lab(s))
