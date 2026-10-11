"""Independent finite audit of the hand proof for MO 508521; standard library.

This checks the proof's intermediate classifications, not just the answer 122.
Run directly: baseline must pass and every deliberately wrong variant must fail.
No search beyond the 4096 subsets of the twelve cube edges is needed.
"""
from collections import Counter
from itertools import combinations, permutations, product
from time import perf_counter

V = list(product((0, 1), repeat=3))
E = [(i, j) for i, j in combinations(range(8), 2)
     if sum(a != b for a, b in zip(V[i], V[j])) == 1]
VI = {v: i for i, v in enumerate(V)}
EI = {frozenset(e): i for i, e in enumerate(E)}
D = [next(j for j in range(3) if V[a][j] != V[b][j]) for a, b in E]
FULL = (1 << 12) - 1


def bits(m):
    return [i for i in range(m.bit_length()) if (m >> i) & 1]


def symmetry_tables():
    answer = []
    for p in permutations(range(3)):
        parity = (-1) ** sum(p[i] > p[j] for i in range(3) for j in range(i+1, 3))
        for f in product((0, 1), repeat=3):
            det = parity * (-1) ** sum(f)
            vp = [VI[tuple(v[p[j]] ^ f[j] for j in range(3))] for v in V]
            ep = [EI[frozenset((vp[a], vp[b]))] for a, b in E]
            images = [0] * (1 << 12)
            for m in range(1, 1 << 12):
                low = m & -m
                images[m] = images[m ^ low] | (1 << ep[low.bit_length()-1])
            answer.append((det, vp, images))
    return answer


G48 = symmetry_tables()
G = [g for g in G48 if g[0] == 1]
assert len(G) == 24 and len(G48) == 48


def data(m):
    adj = [set() for _ in V]
    for i in bits(m):
        a, b = E[i]
        adj[a].add(b)
        adj[b].add(a)
    used = frozenset(i for i in range(8) if adj[i])
    left = set(used)
    components = []
    while left:
        stack = [left.pop()]
        component = set(stack)
        while stack:
            for w in adj[stack.pop()] & left:
                left.remove(w)
                component.add(w)
                stack.append(w)
        components.append(component)
    dims = frozenset(D[i] for i in bits(m))
    return used, components, dims, adj


DATA = [data(m) for m in range(FULL+1)]


def good(m, variant="baseline"):
    used, comps, dims, _ = DATA[m]
    connected = len(comps) == 1
    if variant == "require_all_eight_vertices":
        connected = connected and len(used) == 8
    return (connected and (variant == "retain_planar" or len(dims) == 3)
            and (variant == "retain_full_cube" or m != FULL))


def canonical(m, group=G):
    return min(g[2][m] for g in group)


def orbit_count(ms, group=G):
    return len({canonical(m, group) for m in ms})


def require(label, actual, expected):
    if actual != expected:
        raise AssertionError(f"{label}: got {actual}, expected {expected}")


def tree_on(m, vertices):
    used, comps, _, _ = DATA[m]
    return used == vertices and len(comps) == 1 and m.bit_count() == len(vertices)-1


def audit(variant="baseline"):
    group = G48 if variant == "identify_reflections" else G
    valid = [m for m in range(FULL+1) if good(m, variant)]
    counts = Counter(m.bit_count() for m in {canonical(m, group) for m in valid})
    require("orbit counts k=3..11", [counts[k] for k in range(3,12)],
            [3,5,14,24,32,25,13,5,1])
    require("no other edge counts", sum(counts.values()), 122)
    require("labelled valid sets", len(valid), 2366)

    # The elementary vertex bounds used to rule out two cycles and large splits.
    for n, bound in [(4,4), (5,5), (6,7)]:
        maximum = max(sum(a in S and b in S for a,b in E)
                      for S in map(set, combinations(range(8),n)))
        require(f"induced edge bound on {n} vertices", maximum, bound)

    # Five-edge trees: normalise the pair of unused vertices, and use its stabiliser.
    for distance, pair, labelled, fixed, orbits in [
        (1, (VI[(0,0,0)], VI[(0,0,1)]), 15, [3,15], 9),
        (2, (VI[(0,0,0)], VI[(1,1,0)]), 4, [0,4], 2),
        (3, (VI[(0,0,0)], VI[(1,1,1)]), 6, [0,0,2,2,2,6], 2),
    ]:
        vertices = frozenset(set(range(8))-set(pair))
        trees = [m for m in range(FULL+1) if tree_on(m, vertices)]
        stabiliser = [g for g in G if {g[1][x] for x in pair} == set(pair)]
        fixes = sorted(sum(g[2][m] == m for m in trees) for g in stabiliser)
        require(f"five-tree d={distance} labelled", len(trees), labelled)
        require(f"five-tree d={distance} fixed", fixes, fixed)
        require(f"five-tree d={distance} orbits", orbit_count(trees,stabiliser), orbits)

    # Six-edge trees: a hexagon with a hub attached to alternating vertices.
    missing = VI[(0,0,0)]
    vertices = frozenset(set(range(8))-{missing})
    hub = VI[(1,1,1)]
    spokes = {i for i,e in enumerate(E) if hub in e}
    trees = [m for m in range(FULL+1) if tree_on(m, vertices)]
    by_spokes = Counter(len(set(bits(m)) & spokes) for m in trees)
    stabiliser = [g for g in G if g[1][missing] == missing]
    require("six-tree spoke count", dict(by_spokes), {1:18,2:24,3:8})
    require("six-tree total", len(trees), 48 if variant == "claim_48_six_trees" else 50)
    require("six-tree fixed", sorted(sum(g[2][m] == m for m in trees)
                                    for g in stabiliser),
            [0,0,50] if variant == "claim_zero_third_turn_fixed" else [2,2,50])
    require("six-tree orbits", orbit_count(trees,stabiliser), 18)

    # Check the claimed structural partition of the unicyclic cases.
    for k, expected in [(5,{"square+leaf":1}),
                        (6,{"hexagon, omitted distance 1":1,
                            "hexagon, omitted distance 3":1,
                            "square+two leaves, adjacent":1,
                            "square+two leaves, opposite":1,
                            "square+two-edge tail":2})]:
        families = {}
        for m in valid:
            used, comps, _, adj = DATA[m]
            if m.bit_count() != k or len(used) != k:
                continue
            squares = []
            for axis in range(3):
                for side in (0,1):
                    square = frozenset(i for i,(a,b) in enumerate(E)
                        if V[a][axis] == side and V[b][axis] == side)
                    if all((m >> i) & 1 for i in square):
                        squares.append(square)
            if not squares:
                require("square-free six-cycle", k, 6)
                a,b = set(range(8))-set(used)
                d = sum(x != y for x,y in zip(V[a],V[b]))
                label = f"hexagon, omitted distance {d}"
            else:
                require("unique square", len(squares),1)
                square = squares[0]
                corners = {v for i in square for v in E[i]}
                extra = set(bits(m))-set(square)
                attached = [e for i in extra for e in E[i] if e in corners]
                if k == 5:
                    label = "square+leaf"
                elif len(attached) == 1:
                    label = "square+two-edge tail"
                else:
                    require("two leaves", len(attached),2)
                    a,b = attached
                    d = sum(x != y for x,y in zip(V[a],V[b]))
                    label = "square+two leaves, " + ("adjacent" if d == 1 else "opposite")
            families.setdefault(label,set()).add(canonical(m))
        require(f"{k}-edge unicyclic families", {x:len(y) for x,y in families.items()},expected)
        require(f"{k}-edge cycle rank at most one",
                max(k-len(DATA[m][0])+1 for m in valid if m.bit_count()==k),1)

    # Four-edge trees: branch, or paths whose repeated direction has gap 2 or 3.
    families = {}
    for m in valid:
        if m.bit_count() != 4:
            continue
        used, _, _, adj = DATA[m]
        if max(map(len,adj)) == 3:
            label = "branch"
        else:
            start = next(v for v in used if len(adj[v]) == 1)
            path, prev, at = [], None, start
            while True:
                nxt = adj[at]-({prev} if prev is not None else set())
                if not nxt:
                    break
                to = next(iter(nxt))
                path.append(next(i for i in range(3) if V[at][i]!=V[to][i]))
                prev,at = at,to
            repeated = next(d for d in range(3) if path.count(d) == 2)
            pos = [i for i,d in enumerate(path) if d == repeated]
            label = f"path, repeat gap {pos[1]-pos[0]}"
        families.setdefault(label,set()).add(canonical(m))
    require("four-edge families", {x:len(y) for x,y in families.items()},
            {"branch":2,"path, repeat gap 2":2,"path, repeat gap 3":1})

    # Complement coefficients and the exhaustive large-disconnected classification.
    require("all edge-subset orbit coefficients 0..5",
            [orbit_count(m for m in range(FULL+1) if m.bit_count()==k) for k in range(6)],
            [1,1,5,13,27,38])
    for k, expected in [(7,{(2,6):4,(3,5):1,(4,4):1}),
                        (8,{(2,6):1,(4,4):1}),
                        (9,{}),(10,{}),(11,{})]:
        families = {}
        for m in range(FULL+1):
            _,comps,_,_ = DATA[m]
            if m.bit_count()!=k or len(comps)<=1:
                continue
            sizes = tuple(sorted(map(len,comps)))
            families.setdefault(sizes,set()).add(canonical(m))
        require(f"large disconnected k={k}",{s:len(t) for s,t in families.items()},expected)
    return counts, len(valid)


def main():
    start = perf_counter()
    counts,n = audit()
    print("PASS baseline: 122 rotation classes,",n,"labelled sets")
    print("PASS intermediate counts: 5-edge trees 9+2+2; 6-edge trees (18+24+8+2+2)/3")
    print("PASS unicyclic families, four-edge chirality, induced bounds and large-component partitions")
    mutants = ["identify_reflections","retain_planar","require_all_eight_vertices","retain_full_cube",
               "claim_48_six_trees","claim_zero_third_turn_fixed"]
    for variant in mutants:
        try:
            audit(variant)
        except AssertionError as error:
            group = G48 if variant == "identify_reflections" else G
            total = orbit_count((m for m in range(FULL+1) if good(m,variant)),group)
            print(f"REJECT {variant}: {total} classes; {error}")
        else:
            raise AssertionError(f"Mutation survived: {variant}")
    print(f"All checks and six mutation controls completed in {perf_counter()-start:.3f}s")


if __name__ == "__main__":
    main()
