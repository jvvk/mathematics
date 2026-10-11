"""Finite audit of the hand counts for incomplete open octahedra (185) and tetrahedra (6); standard library.

Checks every intermediate number the note uses, not only the totals, then runs mutation controls:
each deliberately wrong variant must fail an assertion.
"""

from collections import Counter
from itertools import combinations, permutations, product
from time import perf_counter

# Octahedron: vertices +-e_i, an edge joins two vertices that are not antipodal.
OV = [tuple(s if j == i else 0 for j in range(3)) for i in range(3) for s in (1, -1)]
OE = [
    (a, b)
    for a, b in combinations(range(6), 2)
    if sum(x * y for x, y in zip(OV[a], OV[b])) == 0
]
assert len(OE) == 12


def rotations(det_sign=1):
    out = []
    for p in permutations(range(3)):
        par = (-1) ** sum(p[i] > p[j] for i in range(3) for j in range(i + 1, 3))
        for s in product((1, -1), repeat=3):
            if par * s[0] * s[1] * s[2] in ((1,) if det_sign == 1 else (1, -1)):
                out.append((p, s))
    return out


def act(g, v):
    p, s = g
    return tuple(s[i] * v[p[i]] for i in range(3))


def edge_perms(V, E, group):
    vi = {v: i for i, v in enumerate(V)}
    ei = {frozenset(e): k for k, e in enumerate(E)}
    res = []
    for g in group:
        vp = [vi[act(g, v)] for v in V]
        res.append((vp, [ei[frozenset((vp[a], vp[b]))] for a, b in E]))
    return res


def image(m, ep):
    return sum(1 << ep[k] for k in range(len(ep)) if m >> k & 1)


def canon(m, G):
    return min(image(m, ep) for _, ep in G)


def orbits(ms, G):
    return len({canon(m, G) for m in ms})


def bits(m):
    return [k for k in range(m.bit_length()) if m >> k & 1]


def components(m, E):
    adj = {}
    for k in bits(m):
        a, b = E[k]
        adj.setdefault(a, set()).add(b)
        adj.setdefault(b, set()).add(a)
    left, comps = set(adj), []
    while left:
        st = [left.pop()]
        c = set(st)
        while st:
            for w in adj[st.pop()] & left:
                left.remove(w)
                c.add(w)
                st.append(w)
        comps.append(c)
    return adj, comps


def rank3(vs, V):
    P = [V[v] for v in vs]
    if len(P) < 4:
        return False
    rows = [tuple(a - b for a, b in zip(q, P[0])) for q in P[1:]]
    for r1, r2, r3 in combinations(rows, 3):
        det = (
            r1[0] * (r2[1] * r3[2] - r2[2] * r3[1])
            - r1[1] * (r2[0] * r3[2] - r2[2] * r3[0])
            + r1[2] * (r2[0] * r3[1] - r2[1] * r3[0])
        )
        if det:
            return True
    return False


def require(label, got, want):
    if got != want:
        raise AssertionError(f"{label}: got {got}, expected {want}")


def tree_on(m, E, vertices):
    adj, comps = components(m, E)
    return (
        set(adj) == set(vertices)
        and len(comps) == 1
        and len(bits(m)) == len(vertices) - 1
    )


def audit_oct(variant="baseline"):
    G = edge_perms(OV, OE, rotations(1 if variant != "identify_reflections" else 0))
    full = (1 << 12) - 1
    valid = []
    for m in range(1, full + 1):
        adj, comps = components(m, OE)
        ok = (
            len(comps) == 1
            and (variant == "retain_planar" or rank3(set(adj), OV))
            and m != full
        )
        if ok:
            valid.append(m)
    counts = Counter(bin(c).count("1") for c in {canon(m, G) for m in valid})
    require(
        "octahedron counts by edges k=3..11",
        [counts[k] for k in range(3, 12)],
        [5, 16, 34, 46, 38, 27, 13, 5, 1],
    )
    require("octahedron total", sum(counts.values()), 185)

    # Burnside polynomial: identical to the cube's, since the edges correspond under duality.
    require(
        "edge-set orbit coefficients 0..12",
        [
            orbits((m for m in range(full + 1) if bin(m).count("1") == k), G)
            for k in range(13)
        ],
        [1, 1, 5, 13, 27, 38, 48, 38, 27, 13, 5, 1, 1],
    )

    # Induced edges: 2, 3, 4 vertices span at most 1, 3, 5 edges; five exactly when one antipodal pair.
    span = lambda S: sum(a in S and b in S for a, b in OE)
    for n, bound in [(2, 1), (3, 3), (4, 5)]:
        require(
            f"induced bound on {n} vertices",
            max(span(set(S)) for S in combinations(range(6), n)),
            bound,
        )
    anti = lambda S: sum(
        OV[a] == tuple(-x for x in OV[b]) for a, b in combinations(S, 2)
    )
    require(
        "4-sets with 5 edges have one antipodal pair",
        {anti(S) for S in combinations(range(6), 4) if span(set(S)) == 5},
        {1},
    )
    require(
        "4-sets with 2 antipodal pairs are coplanar squares",
        {
            (span(set(S)), rank3(S, OV))
            for S in combinations(range(6), 4)
            if anti(S) == 2
        },
        {(4, False)},
    )

    # Disconnected classification by component vertex sizes, k = 4..11.
    want = {5: {(2, 4): 3, (3, 3): 1}, 6: {(2, 4): 1, (3, 3): 1}}
    for k in range(5, 12):
        fam = {}
        for m in range(full + 1):
            if bin(m).count("1") != k:
                continue
            _, comps = components(m, OE)
            if len(comps) > 1:
                fam.setdefault(tuple(sorted(map(len, comps))), set()).add(canon(m, G))
        require(
            f"disconnected k={k}", {s: len(t) for s, t in fam.items()}, want.get(k, {})
        )

    # k = 4: three cyclic types on a four-set with one antipodal pair; thirteen trees.
    cyc = [
        m for m in valid if bin(m).count("1") == 4 and len(components(m, OE)[0]) == 4
    ]
    shapes = Counter()
    for c in {canon(m, G) for m in cyc}:
        adj, _ = components(c, OE)
        shapes[
            "4-cycle" if all(len(x) == 2 for x in adj.values()) else "triangle+pendant"
        ] += 1
    require("k=4 cyclic shapes", dict(shapes), {"4-cycle": 1, "triangle+pendant": 2})
    missing = OV.index((0, 0, -1))
    hub = OV.index((0, 0, 1))
    rest = set(range(6)) - {missing}
    wheel_trees = [m for m in range(full + 1) if tree_on(m, OE, rest)]
    spokes = {k for k, e in enumerate(OE) if hub in e}
    require(
        "wheel trees by spokes",
        dict(Counter(len(set(bits(m)) & spokes) for m in wheel_trees)),
        {1: 16, 2: 20, 3: 8, 4: 1},
    )
    require(
        "wheel trees", len(wheel_trees), 44 if variant == "claim_44_wheel_trees" else 45
    )
    stab = [g for g in G if g[0][missing] == missing]
    require("wheel stabiliser order", len(stab), 4)
    require(
        "wheel fixed counts",
        sorted(sum(image(m, ep) == m for m in wheel_trees) for _, ep in stab),
        [1, 1, 3, 45] if variant == "claim_3_half_turn_fixed" else [1, 1, 5, 45],
    )
    require("wheel tree orbits", orbits(wheel_trees, stab), 13)

    # k = 3: trees on a four-set with one antipodal pair (K4 minus an edge); twelve such sets, one orbit.
    S = [OV.index(v) for v in [(0, 0, 1), (0, 0, -1), (-1, 0, 0), (0, -1, 0)]]
    k4e = [m for m in range(full + 1) if tree_on(m, OE, S)]
    require("K4-e trees", len(k4e), 8)
    stab = [g for g in G if {g[0][x] for x in S} == set(S)]
    require(
        "K4-e fixed",
        sorted(sum(image(m, ep) == m for m in k4e) for _, ep in stab),
        [2, 8],
    )
    require("K4-e orbits", orbits(k4e, stab), 5)
    require(
        "spatial 4-sets", sum(1 for T in combinations(range(6), 4) if rank3(T, OV)), 12
    )
    return counts


# Tetrahedron: four vertices of a regular tetrahedron; every 4-set spans 3-space.
TV = [(1, 1, 1), (1, -1, -1), (-1, 1, -1), (-1, -1, 1)]
TE = list(combinations(range(4), 2))


def tet_group(variant):
    # Rotations act on the four vertices as the even permutations.
    perms = [
        p
        for p in permutations(range(4))
        if variant == "identify_reflections"
        or sum(p[i] > p[j] for i in range(4) for j in range(i + 1, 4)) % 2 == 0
    ]
    ei = {frozenset(e): k for k, e in enumerate(TE)}
    return [(list(p), [ei[frozenset((p[a], p[b]))] for a, b in TE]) for p in perms]


def audit_tet(variant="baseline"):
    G = tet_group(variant)
    full = (1 << 6) - 1
    valid = [
        m
        for m in range(1, full + 1)
        if len(components(m, TE)[1]) == 1
        and m != full
        and (variant == "retain_planar" or len(components(m, TE)[0]) == 4)
    ]
    counts = Counter(bin(c).count("1") for c in {canon(m, G) for m in valid})
    require("tetrahedron counts k=3..5", [counts[k] for k in range(3, 6)], [3, 2, 1])
    trees = [m for m in valid if bin(m).count("1") == 3]
    require("K4 trees", len(trees), 16)
    stars = [m for m in trees if max(map(len, components(m, TE)[0].values())) == 3]
    require("stars, paths", (len(stars), len(trees) - len(stars)), (4, 12))
    require(
        "star orbits, path orbits",
        (orbits(stars, G), orbits([m for m in trees if m not in stars], G)),
        (1, 2),
    )
    return counts


def main():
    t = perf_counter()
    c = audit_oct()
    print("PASS octahedron:", sum(c.values()), dict(sorted(c.items())))
    c = audit_tet()
    print("PASS tetrahedron:", sum(c.values()), dict(sorted(c.items())))
    for audit, variant in [
        (audit_oct, "identify_reflections"),
        (audit_oct, "retain_planar"),
        (audit_oct, "claim_44_wheel_trees"),
        (audit_oct, "claim_3_half_turn_fixed"),
        (audit_tet, "identify_reflections"),
        (audit_tet, "retain_planar"),
    ]:
        try:
            audit(variant)
        except AssertionError as e:
            print(f"REJECT {audit.__name__} {variant}: {e}")
        else:
            raise AssertionError(f"mutation survived: {audit.__name__} {variant}")
    print(f"all checks and six mutation controls passed in {perf_counter() - t:.1f}s")


if __name__ == "__main__":
    main()
