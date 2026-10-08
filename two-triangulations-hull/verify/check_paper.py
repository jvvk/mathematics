"""Exact checks for "Two Triangulations That Share Only Their Hull".

Python 3.9+, standard library only, integer arithmetic throughout (rationals for p = (24, 24)).
Independent of the search code in enumeration/. Prints a JSON summary; exits non-zero on any failure.

Checks:
  1. Section 3: the nine-point example (general position, pentagonal hull, both layers are triangulations,
     common edges = hull edges).
  2. Section 4: (24, 24) lies in faces 156 of A and 479 of B and on no line through two points; good pair.
  3. Section 5 example: side 56 of 156 meets the faces 357, 347, 479, 469 of B in that order; after the
     insertion, face 56p of A' and face 347 of B' form a good pair.
  4. Lemma 2 figure: in the triangular-hull example, q is the unique point nearest to m and uq is crossed by
     no segment.
  5. Section 6 formula: min |A ∩ B| = 6n - 6 - 2h - C(n,2) + oct(P), compared with brute force over all pairs
     of triangulations, on every 5-, 6- and 7-point subset of the nine-point set and on the convex pentagon.
  6. Certificates n = 9..17 (certificates/*.json): two triangulations sharing exactly the five hull edges.
  9. Chains (Section 5): (156; 479, 347) along 56; after inserting (24,24) the chain (56p; 347, 47p); the convex
     seed has the chain (v1v3v5; v2v4v6, v2v6v7) for h = 7..30 and no chain at all for h = 6; the seven-point
     example has the chain (137; 245, 267).
  8. Section 7: Lemma 9 (convex seed) for h = 6..30 on y = x^2, the pentagon fans, and the seven-point
     hexagonal example with the good pair 137, 245 and the point (6/5, 2/5) inside both.
  7. The seven nine-point witnesses (witnesses09.txt): pentagonal hull, oct = 3 so the minimum is exactly 5,
     trivial combinatorial automorphism group, and the Section 3 set has the order type of one of them.
"""

from __future__ import annotations

import itertools
import json
import re
import sys
from fractions import Fraction
from pathlib import Path

HERE = Path(__file__).parent
summary: dict = {}


def fail(msg: str) -> None:
    print(json.dumps({"FAILED": msg, **summary}, indent=1))
    sys.exit(1)


def check(cond: bool, msg: str) -> None:
    if not cond:
        fail(msg)


# ---------------------------------------------------------------- geometry
def orient(p, q, r) -> int:
    v = (q[0] - p[0]) * (r[1] - p[1]) - (q[1] - p[1]) * (r[0] - p[0])
    return (v > 0) - (v < 0)


def general_position(P) -> bool:
    return all(orient(a, b, c) != 0 for a, b, c in itertools.combinations(P, 3))


def proper_cross(P, e, f) -> bool:
    a, b = P[e[0]], P[e[1]]
    c, d = P[f[0]], P[f[1]]
    if len({e[0], e[1], f[0], f[1]}) < 4:
        return False
    return (
        orient(a, b, c) * orient(a, b, d) < 0 and orient(c, d, a) * orient(c, d, b) < 0
    )


def hull_cycle(P) -> list[int]:
    idx = sorted(range(len(P)), key=lambda i: P[i])

    def chain(seq):
        out: list[int] = []
        for i in seq:
            while len(out) >= 2 and orient(P[out[-2]], P[out[-1]], P[i]) <= 0:
                out.pop()
            out.append(i)
        return out

    lo, up = chain(idx), chain(idx[::-1])
    return lo[:-1] + up[:-1]


def hull_edges(P) -> set:
    cyc = hull_cycle(P)
    return {tuple(sorted((cyc[i], cyc[(i + 1) % len(cyc)]))) for i in range(len(cyc))}


def is_triangulation(P, E) -> bool:
    E = {tuple(sorted(e)) for e in E}
    h = len(hull_cycle(P))
    if len(E) != 3 * len(P) - 3 - h:
        return False
    return not any(proper_cross(P, e, f) for e, f in itertools.combinations(E, 2))


def faces(P, E) -> list[tuple]:
    E = {tuple(sorted(e)) for e in E}
    out = []
    for t in itertools.combinations(range(len(P)), 3):
        if all(tuple(sorted(x)) in E for x in itertools.combinations(t, 2)):
            if not any(
                strictly_inside(P, t, P[v]) for v in range(len(P)) if v not in t
            ):
                out.append(t)
    return out


def strictly_inside(P, t, q) -> bool:
    a, b, c = (P[i] for i in t)
    s = [orient(a, b, q), orient(b, c, q), orient(c, a, q)]
    return all(x > 0 for x in s) or all(x < 0 for x in s)


def ccw(P, t):
    a, b, c = t
    return (a, b, c) if orient(P[a], P[b], P[c]) > 0 else (a, c, b)


def interiors_meet(P, s, t) -> bool:
    """Two triangles have intersecting interiors iff no side line weakly separates them."""
    for u, w in ((s, t), (t, s)):
        x, y, z = ccw(P, u)
        for a, b in ((x, y), (y, z), (z, x)):
            if all(orient(P[a], P[b], P[v]) <= 0 for v in w):
                return False
    return True


def good_pair(P, s, t) -> bool:
    return not set(s) & set(t) and interiors_meet(P, s, t)


def faces_along(P, F, x, y) -> list[tuple]:
    """Faces whose interior meets the open segment xy, ordered from x to y (exact parametric intervals)."""
    X, Y = P[x], P[y]
    hits = []
    for f in F:
        a, b, c = (P[i] for i in ccw(P, f))
        lo, hi = Fraction(0), Fraction(1)
        ok = True
        for u, v in ((a, b), (b, c), (c, a)):
            # cross(v - u, (X + t (Y - X)) - u) > 0  is linear in t: g0 + g1 t > 0
            g0 = (v[0] - u[0]) * (X[1] - u[1]) - (v[1] - u[1]) * (X[0] - u[0])
            g1 = (v[0] - u[0]) * (Y[1] - X[1]) - (v[1] - u[1]) * (Y[0] - X[0])
            if g1 == 0:
                ok = ok and g0 > 0
            elif g1 > 0:
                lo = max(lo, Fraction(-g0, g1))
            else:
                hi = min(hi, Fraction(-g0, g1))
        if ok and lo < hi:
            hits.append((lo, f))
    return [f for _, f in sorted(hits)]


def crossing_graph(P):
    S = list(itertools.combinations(range(len(P)), 2))
    adj = {i: set() for i in range(len(S))}
    for i, j in itertools.combinations(range(len(S)), 2):
        if proper_cross(P, S[i], S[j]):
            adj[i].add(j)
            adj[j].add(i)
    return S, adj


def bipartite(adj, removed) -> bool:
    col = {}
    for s in adj:
        if s in removed or s in col:
            continue
        col[s] = 0
        stack = [s]
        while stack:
            u = stack.pop()
            for v in adj[u]:
                if v in removed:
                    continue
                if v not in col:
                    col[v] = 1 - col[u]
                    stack.append(v)
                elif col[v] == col[u]:
                    return False
    return True


def oct_number(P, kmax=6) -> int:
    S, adj = crossing_graph(P)
    live = [s for s in adj if adj[s]]
    for k in range(kmax + 1):
        if any(bipartite(adj, set(r)) for r in itertools.combinations(live, k)):
            return k
    fail("oct search exceeded kmax")


def triangulations(P) -> list[frozenset]:
    """All triangulations: independent sets of the crossing graph of size 3n-3-h."""
    S, adj = crossing_graph(P)
    target = 3 * len(P) - 3 - len(hull_cycle(P))
    forced = [s for s in adj if not adj[s]]
    rest = [s for s in adj if adj[s]]
    out = []

    def rec(i, chosen):
        if len(forced) + len(chosen) == target:
            out.append(frozenset(S[s] for s in forced + chosen))
            return
        if i == len(rest) or len(forced) + len(chosen) + (len(rest) - i) < target:
            return
        s = rest[i]
        if not any(t in adj[s] for t in chosen):
            rec(i + 1, chosen + [s])
        rec(i + 1, chosen)

    rec(0, [])
    return out


def min_shared_brute(P) -> int:
    T = triangulations(P)
    return min(len(a & b) for a in T for b in T)


def min_shared_formula(P) -> int:
    n, h = len(P), len(hull_cycle(P))
    return 6 * n - 6 - 2 * h - n * (n - 1) // 2 + oct_number(P)


def automorphisms(P) -> list[tuple]:
    """Bijections preserving all orientations (+1) or reversing all (-1)."""
    n = len(P)
    H = hull_cycle(P)
    h = len(H)
    inner = [i for i in range(n) if i not in H]
    found = []
    for shift in range(h):
        for direction in (1, -1):
            hullmap = {H[i]: H[(shift + direction * i) % h] for i in range(h)}
            for perm in itertools.permutations(inner):
                pi = dict(hullmap)
                pi.update(zip(inner, perm))
                for sign in (1, -1):
                    if all(
                        orient(P[pi[a]], P[pi[b]], P[pi[c]])
                        == sign * orient(P[a], P[b], P[c])
                        for a, b, c in itertools.combinations(range(n), 3)
                    ):
                        found.append((sign, tuple(pi[i] for i in range(n))))
    return found


def same_order_type(P, Q) -> bool:
    """Is there a bijection P -> Q preserving all orientations or reversing all? (hull-cyclic candidates)"""
    if len(P) != len(Q):
        return False
    HP, HQ = hull_cycle(P), hull_cycle(Q)
    if len(HP) != len(HQ):
        return False
    h, n = len(HP), len(P)
    ip = [i for i in range(n) if i not in HP]
    iq = [i for i in range(n) if i not in HQ]
    triples = list(itertools.combinations(range(n), 3))
    for shift in range(h):
        for direction in (1, -1):
            base = {HP[i]: HQ[(shift + direction * i) % h] for i in range(h)}
            for perm in itertools.permutations(iq):
                pi = dict(base)
                pi.update(zip(ip, perm))
                for sign in (1, -1):
                    if all(
                        orient(Q[pi[a]], Q[pi[b]], Q[pi[c]])
                        == sign * orient(P[a], P[b], P[c])
                        for a, b, c in triples
                    ):
                        return True
    return False


# ---------------------------------------------------------------- 1. nine points
P9 = [
    (33, 47),
    (47, 30),
    (47, 5),
    (29, 20),
    (28, 26),
    (21, 21),
    (23, 29),
    (2, 0),
    (0, 31),
]
lab = {str(i + 1): i for i in range(9)}


def E(spec: str) -> set:
    return {tuple(sorted((lab[s[0]], lab[s[1]]))) for s in spec.split()}


HULL = E("12 23 38 89 91")
A = HULL | E("14 15 16 17 18 24 28 45 48 56 58 67 68 78")
B = HULL | E("25 27 29 34 35 36 37 39 46 47 49 57 69 79")
check(general_position(P9), "nine points not in general position")
check(hull_edges(P9) == HULL, "hull is not the pentagon 1,2,3,8,9")
check(len(A) == len(B) == 19 == 3 * 9 - 3 - 5, "edge counts")
check(
    is_triangulation(P9, A) and is_triangulation(P9, B), "A or B is not a triangulation"
)
check(A & B == HULL, "A and B share an interior edge")
summary["section3_nine_points"] = "ok"

# ---------------------------------------------------------------- 2. insertion at (24, 24)
FA, FB = faces(P9, A), faces(P9, B)
alpha, beta = tuple(sorted(lab[c] for c in "156")), tuple(sorted(lab[c] for c in "479"))
check(alpha in FA and beta in FB, "156 / 479 are not faces")
p = (24, 24)
check(
    strictly_inside(P9, alpha, p) and strictly_inside(P9, beta, p),
    "(24,24) not inside 156 and 479",
)
check(
    all(orient(P9[i], P9[j], p) != 0 for i, j in itertools.combinations(range(9), 2)),
    "(24,24) on a line through two points",
)
check(good_pair(P9, alpha, beta), "156, 479 not a good pair")
all_good = [(f, g) for f in FA for g in FB if good_pair(P9, f, g)]
summary["section4_insertion"] = {"good_pairs_n9": len(all_good)}

# ---------------------------------------------------------------- 3. the good pair returns (example)
x, y = lab["5"], lab["6"]
along = ["".join(str(i + 1) for i in sorted(f)) for f in faces_along(P9, FB, x, y)]
check(along == ["357", "347", "479", "469"], f"faces met by side 56: {along}")
P10 = P9 + [p]
q = 9
A2 = A | {tuple(sorted((i, q))) for i in alpha}
B2 = B | {tuple(sorted((i, q))) for i in beta}
check(general_position(P10), "P + p not in general position")
check(
    is_triangulation(P10, A2) and is_triangulation(P10, B2) and A2 & B2 == HULL,
    "insertion step",
)
FA2, FB2 = faces(P10, A2), faces(P10, B2)
f56p = tuple(sorted((x, y, q)))
f347 = tuple(sorted(lab[c] for c in "347"))
check(
    f56p in FA2 and f347 in FB2 and good_pair(P10, f56p, f347),
    "56p, 347 not a good pair",
)
summary["section5_example"] = {
    "side_56_faces_of_B": along,
    "new_good_pair": "56p,347",
    "good_pairs_after_insertion": sum(good_pair(P10, f, g) for f in FA2 for g in FB2),
}

# ---------------------------------------------------------------- 4. Lemma 2 figure
U, V, W, Q, R, T = (0, 0), (12, 0), (0, 12), (2, 3), (5, 3), (3, 6)
SP = [U, V, W, Q, R, T]
check(general_position(SP) and len(hull_cycle(SP)) == 3, "sweep example")
d = {
    i: SP[i][0] + SP[i][1] for i in range(1, 6)
}  # distance to m: x + y = 0 (times sqrt 2)
check(
    min(d, key=d.get) == 3 and sorted(d.values())[1] > d[3],
    "q not the unique nearest point",
)
uq = (0, 3)
check(
    not any(proper_cross(SP, uq, e) for e in itertools.combinations(range(6), 2)),
    "uq is crossed",
)
summary["lemma2_figure"] = "ok"

# ---------------------------------------------------------------- 5. the formula, brute force
tested = 0
for k in (5, 6, 7):
    for sub in itertools.combinations(range(9), k):
        Psub = [P9[i] for i in sub]
        check(
            min_shared_brute(Psub) == min_shared_formula(Psub),
            f"formula fails on subset {sub}",
        )
        tested += 1
PENT = [(0, 10), (10, 3), (6, -8), (-6, -8), (-10, 3)]
check(
    oct_number(PENT) == 1 and min_shared_formula(PENT) == 5 == min_shared_brute(PENT),
    "convex pentagon",
)
summary["section6_formula"] = {
    "point_sets_tested": tested + 1,
    "convex_pentagon_oct": 1,
}

# ---------------------------------------------------------------- 6. certificates n = 9..17
certs = {}
for fpath in sorted((HERE / "certificates").glob("n*.json")):
    c = json.loads(fpath.read_text())
    Pc = [tuple(pt) for pt in c["points"]]
    Ac = {tuple(sorted(e)) for e in c["A"]}
    Bc = {tuple(sorted(e)) for e in c["B"]}
    Hc = hull_edges(Pc)
    check(
        general_position(Pc) and len(Hc) == 5,
        f"{fpath.name}: general position / pentagonal hull",
    )
    check(
        is_triangulation(Pc, Ac) and is_triangulation(Pc, Bc),
        f"{fpath.name}: not triangulations",
    )
    check(Ac & Bc == Hc, f"{fpath.name}: shared edges are not exactly the hull")
    certs[len(Pc)] = "ok"
check(
    sorted(certs) == list(range(9, 18)), f"certificates found for n = {sorted(certs)}"
)
summary["certificates"] = certs

# ---------------------------------------------------------------- 7. the seven nine-point witnesses
wit = []
for line in (HERE / "witnesses09.txt").read_text().splitlines():
    pts = [(int(a), int(b)) for a, b in re.findall(r"\((\d+),(\d+)\)", line)]
    if pts:
        wit.append(pts)
check(len(wit) == 7, "expected seven witnesses")
for Pw in wit:
    check(
        general_position(Pw) and len(hull_cycle(Pw)) == 5,
        "witness: hull is not a pentagon",
    )
    check(
        oct_number(Pw) == 3 and min_shared_formula(Pw) == 5, "witness: minimum is not 5"
    )
    auts = automorphisms(Pw)
    check(
        auts == [(1, tuple(range(9)))],
        f"witness has a nontrivial automorphism: {auts[:3]}",
    )
check(
    sum(same_order_type(P9, Pw) for Pw in wit) == 1,
    "Section 3 set is not exactly one of the seven",
)
summary["witnesses09"] = {
    "count": 7,
    "hull": 5,
    "oct": 3,
    "min_shared": 5,
    "automorphisms": "trivial",
    "section3_set_matches": 1,
}

# ---------------------------------------------------------------- 8. Section 7: other hulls
def cyc_edges(idx):
    return {tuple(sorted((idx[i], idx[(i + 1) % len(idx)]))) for i in range(len(idx))}


seeds = []
for h in range(6, 31):
    Pc = [(i, i * i) for i in range(h)]          # convex position; hull order v_1..v_h = 0..h-1
    Hc = hull_edges(Pc)
    check(general_position(Pc) and Hc == cyc_edges(list(range(h))), f"convex seed h={h}: hull")
    Ac = Hc | {(0, 2), (2, 4), (0, 4)} | {(4, k) for k in range(6, h)}
    Bc = Hc | {(1, 3), (3, 5), (1, 5)} | {(1, k) for k in range(6, h)}
    check(is_triangulation(Pc, Ac) and is_triangulation(Pc, Bc), f"convex seed h={h}: not triangulations")
    check(Ac & Bc == Hc, f"convex seed h={h}: shared interior edge")
    check((0, 2, 4) in faces(Pc, Ac) and (1, 3, 5) in faces(Pc, Bc), f"convex seed h={h}: faces")
    check(good_pair(Pc, (0, 2, 4), (1, 3, 5)), f"convex seed h={h}: no good pair")
    seeds.append(h)
PENT5 = [(i, i * i) for i in range(5)]
H5 = hull_edges(PENT5)
A5, B5 = H5 | {(0, 2), (0, 3)}, H5 | {(1, 3), (1, 4)}
check(is_triangulation(PENT5, A5) and is_triangulation(PENT5, B5) and A5 & B5 == H5, "pentagon fans")

S7 = [(1, 2), (0, 0), (1, 0), (4, 1), (5, 2), (6, 6), (2, 1)]
lab7 = {str(i + 1): i for i in range(7)}


def E7(spec: str) -> set:
    return {tuple(sorted((lab7[t[0]], lab7[t[1]]))) for t in spec.split()}


H7 = E7("12 23 34 45 56 16")
A7 = H7 | E7("13 14 15 17 37 47")
B7 = H7 | E7("24 25 26 27 57 67")
check(general_position(S7) and hull_edges(S7) == H7, "seven points: hull is not the hexagon 1..6")
check(len(A7) == len(B7) == 12 == 3 * 7 - 3 - 6, "seven points: edge counts")
check(is_triangulation(S7, A7) and is_triangulation(S7, B7) and A7 & B7 == H7, "seven points: triangulations")
f137, f245 = (0, 2, 6), (1, 3, 4)
check(f137 in faces(S7, A7) and f245 in faces(S7, B7) and good_pair(S7, f137, f245), "seven points: 137, 245")
w = (Fraction(6, 5), Fraction(2, 5))
check(strictly_inside(S7, f137, w) and strictly_inside(S7, f245, w), "seven points: (6/5,2/5) not inside both")
summary["section7_other_hulls"] = {
    "convex_seed_h": f"{seeds[0]}..{seeds[-1]}",
    "pentagon_fans": "ok",
    "seven_points": "ok",
    "good_pairs_seven": sum(good_pair(S7, f, g) for f in faces(S7, A7) for g in faces(S7, B7)),
}

# ---------------------------------------------------------------- 9. chains
def chains(P, A, B):
    """All chains (alpha; beta, gamma) along a non-hull side xy of a face alpha of A."""
    H = hull_edges(P)
    FA, FB = faces(P, A), faces(P, B)
    out = []
    for al in FA:
        for x, y in itertools.combinations(al, 2):
            if tuple(sorted((x, y))) in H:
                continue
            along = faces_along(P, FB, x, y)
            for be in along:
                if set(be) & set(al):
                    continue
                for ga in along:
                    if ga != be and x not in ga and y not in ga:
                        out.append((al, (x, y), be, ga))
    return out


def has_chain(P, A, B, al, xy, be, ga):
    return (tuple(sorted(al)), tuple(sorted(xy)), tuple(sorted(be)), tuple(sorted(ga))) in {
        (tuple(sorted(a)), tuple(sorted(e)), tuple(sorted(b)), tuple(sorted(g))) for a, e, b, g in chains(P, A, B)}


L9 = lambda w: tuple(lab[c] for c in w)
check(has_chain(P9, A, B, L9("156"), L9("56"), L9("479"), L9("347")), "nine points: no chain (156;479,347)")
check(has_chain(P10, A2, B2, (x, y, q), (x, y), f347, (lab["4"], lab["7"], q)), "after insertion: no chain (56p;347,47p)")
conv = []
for h in range(6, 31):
    Pc = [(i, i * i) for i in range(h)]
    Hc = hull_edges(Pc)
    Ac = Hc | {(0, 2), (2, 4), (0, 4)} | {(4, k) for k in range(6, h)}
    Bc = Hc | {(1, 3), (3, 5), (1, 5)} | {(1, k) for k in range(6, h)}
    if h == 6:
        check(chains(Pc, Ac, Bc) == [], "convex seed h=6 has a chain")
    else:
        check(has_chain(Pc, Ac, Bc, (0, 2, 4), (0, 2), (1, 3, 5), (1, 5, 6)), f"convex seed h={h}: no chain")
    conv.append(h)
check(has_chain(S7, A7, B7, (0, 2, 6), (0, 2), (1, 3, 4), (1, 5, 6)), "seven points: no chain (137;245,267)")
# remark after Theorem 2: in the hexagon seed the good pair (v1v3v5, v2v4v6) does not return after an insertion
P6 = [(i, i * i) for i in range(6)]
H6 = hull_edges(P6)
A6, B6 = H6 | {(0, 2), (2, 4), (0, 4)}, H6 | {(1, 3), (3, 5), (1, 5)}
hex_tested = 0
for i in range(0, 41):
    for j in range(0, 201):
        pt = (Fraction(i, 8), Fraction(j, 8))
        if not (strictly_inside(P6, (0, 2, 4), pt) and strictly_inside(P6, (1, 3, 5), pt)):
            continue
        if any(orient(P6[a], P6[b], pt) == 0 for a, b in itertools.combinations(range(6), 2)):
            continue
        Q6 = P6 + [pt]
        A6p = A6 | {(v, 6) for v in (0, 2, 4)}
        B6p = B6 | {(v, 6) for v in (1, 3, 5)}
        check(not any(good_pair(Q6, f, g) for f in faces(Q6, A6p) for g in faces(Q6, B6p)),
              f"hexagon seed keeps a good pair after inserting {pt}")
        hex_tested += 1
check(hex_tested > 100, "too few hexagon insertion points tested")
summary["chains"] = {"nine": "(156;479,347)", "after_insertion": "(56p;347,47p)",
                     "convex_h6_chains": 0, "hexagon_insertions_without_good_pair": hex_tested, "convex_chain_h": "7..30", "seven": "(137;245,267)"}

print(json.dumps({"all_checks": "passed", **summary}, indent=1))
