"""Exact plane geometry used by the figures and the checker (standard library only)."""
from __future__ import annotations

import itertools
from fractions import Fraction as Fr


def cr(o, a, b):
    """Twice the signed area of triangle o a b: positive if o -> a -> b turns left."""
    return (a[0] - o[0]) * (b[1] - o[1]) - (a[1] - o[1]) * (b[0] - o[0])


def crosses(p, q, r, s) -> bool:
    """Do the open segments pq and rs cross at a single interior point?"""
    return cr(p, q, r) * cr(p, q, s) < 0 and cr(r, s, p) * cr(r, s, q) < 0


def hull_edges(pts):
    """Edges of the convex hull (Andrew's monotone chain), as sorted index pairs."""
    idx = sorted(range(len(pts)), key=lambda i: pts[i])

    def chain(order):
        h = []
        for i in order:
            while len(h) >= 2 and cr(pts[h[-2]], pts[h[-1]], pts[i]) <= 0:
                h.pop()
            h.append(i)
        return h

    lo, up = chain(idx), chain(idx[::-1])
    cyc = lo[:-1] + up[:-1]
    return {tuple(sorted((cyc[k], cyc[(k + 1) % len(cyc)]))) for k in range(len(cyc))}


def oriented(P, t):
    a, b, c = t
    return (a, b, c) if cr(P[a], P[b], P[c]) > 0 else (a, c, b)


def faces_of(E, P):
    """Faces of a triangulation: 3-cycles of the edge set with no point of P strictly inside."""
    n = len(P)
    adj = {i: set() for i in range(n)}
    for a, b in E:
        adj[a].add(b)
        adj[b].add(a)
    out = []
    for t in itertools.combinations(range(n), 3):
        if t[1] in adj[t[0]] and t[2] in adj[t[0]] and t[2] in adj[t[1]]:
            a, b, c = oriented(P, t)
            if not any(cr(P[a], P[b], P[v]) > 0 and cr(P[b], P[c], P[v]) > 0 and cr(P[c], P[a], P[v]) > 0
                       for v in range(n) if v not in t):
                out.append(t)
    return out


def separated(P, s, t) -> bool:
    """Do triangles s and t have disjoint interiors? (some side line of one has the other weakly outside)"""
    for u, v in ((s, t), (t, s)):
        x, y, z = oriented(P, u)
        for a, b in ((x, y), (y, z), (z, x)):
            if all(cr(P[a], P[b], P[w]) <= 0 for w in v):
                return True
    return False


def good_pairs(P, FA, FB):
    return [(s, t) for s in FA for t in FB if not set(s) & set(t) and not separated(P, s, t)]


def clip(poly, a, b):
    out = []
    for i in range(len(poly)):
        p, q = poly[i], poly[(i + 1) % len(poly)]
        sp, sq = cr(a, b, p), cr(a, b, q)
        if sp >= 0:
            out.append(p)
        if (sp >= 0) != (sq >= 0):
            k = Fr(sp, sp - sq)
            out.append((p[0] + k * (q[0] - p[0]), p[1] + k * (q[1] - p[1])))
    return out


def overlap(P, s, t):
    """The polygon s & t (exact rational vertices)."""
    poly = [(Fr(P[v][0]), Fr(P[v][1])) for v in oriented(P, s)]
    T = [(Fr(P[v][0]), Fr(P[v][1])) for v in oriented(P, t)]
    for i in range(3):
        poly = clip(poly, T[i], T[(i + 1) % 3])
    return poly


def area(poly):
    return abs(sum(poly[i][0] * poly[(i + 1) % len(poly)][1] - poly[(i + 1) % len(poly)][0] * poly[i][1]
                   for i in range(len(poly)))) / 2


def general_position(P) -> bool:
    return all(cr(P[a], P[b], P[c]) != 0 for a, b, c in itertools.combinations(range(len(P)), 3))
