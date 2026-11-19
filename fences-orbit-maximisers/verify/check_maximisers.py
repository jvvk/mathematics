"""Compare the maximisers found by search.sh (search_out.txt) with Theorem 1, up to isomorphism.
Each maximiser is split into connected components; a component is named by brute-force isomorphism with
a fence Z_m, with Q, its dual Q*, or with R. Exits nonzero on any difference. Run: python3 -I check_maximisers.py"""
import itertools
import sys

EXPECTED = {
    1: [["pt"]], 2: [["Z2"], ["pt", "pt"]], 3: [["Z2", "pt"]], 4: [["Z2", "pt", "pt"]],
    5: [["Z4", "pt"]], 6: [["Z2", "Z4"], ["Z4", "pt", "pt"]], 7: [["Z2", "Z4", "pt"]],
    8: [["Q", "pt"], ["Q*", "pt"]], 9: [["Z2", "Z6", "pt"]],
    10: [["Q", "Z2", "pt"], ["Q*", "Z2", "pt"]], 11: [["R", "Z2", "pt"]],
}


def decode(g6: str) -> tuple[int, set[tuple[int, int]]]:
    s = g6.lstrip("&")
    n = ord(s[0]) - 63
    bits = [(ord(c) - 63) >> (5 - i) & 1 for c in s[1:] for i in range(6)]
    return n, {(i, j) for i in range(n) for j in range(n) if bits[i * n + j]}


def closure(covers: set[tuple[int, int]]) -> set[tuple[int, int]]:
    lt = set(covers)
    while True:
        new = {(a, d) for a, b in lt for c, d in lt if b == c} - lt
        if not new:
            return lt
        lt |= new


def isomorphic(n: int, lt1: set, lt2: set) -> bool:
    if len(lt1) != len(lt2):
        return False
    return any({(p[a], p[b]) for a, b in lt1} == lt2 for p in itertools.permutations(range(n)))


def relabel(elems: list[int], pairs: set) -> set:
    idx = {v: i for i, v in enumerate(elems)}
    return {(idx[a], idx[b]) for a, b in pairs if a in idx and b in idx}


def fence(m: int) -> set:
    return closure({(i, i + 1) if i % 2 == 0 else (i + 1, i) for i in range(m - 1)})


Q = closure({(0, 1), (2, 1), (2, 3), (4, 3), (4, 5), (6, 3)})
NAMED = {"Q": (7, Q), "Q*": (7, {(b, a) for a, b in Q}),
         "R": (8, closure({(0, 1), (2, 1), (2, 3), (4, 3), (4, 5), (6, 3), (2, 7)}))}


def name(m: int, lt: set) -> str:
    if m == 1:
        return "pt"
    if m % 2 == 0 and isomorphic(m, lt, fence(m)):
        return f"Z{m}"
    for key, (k, rel) in NAMED.items():
        if k == m and isomorphic(m, lt, rel):
            return key
    return f"other{m}"


def components(n: int, covers: set) -> list[list[int]]:
    adj = {v: set() for v in range(n)}
    for a, b in covers:
        adj[a].add(b)
        adj[b].add(a)
    seen, out = set(), []
    for v in range(n):
        if v not in seen:
            stack, comp = [v], set()
            while stack:
                x = stack.pop()
                if x not in comp:
                    comp.add(x)
                    stack += adj[x]
            seen |= comp
            out.append(sorted(comp))
    return out


def describe(g6: str) -> list[str]:
    n, covers = decode(g6)
    lt = closure(covers)
    return sorted(name(len(c), relabel(c, lt)) for c in components(n, covers))


ok = True
rows = [ln for ln in open(sys.argv[1] if len(sys.argv) > 1 else "search_out.txt") if ln.strip()]
seen = [int(ln.split()[0]) for ln in rows]
if not rows or seen != list(range(1, len(rows) + 1)):
    sys.exit(f"FAILED: expected rows n = 1, 2, ..., got {seen}")
for line in rows:
    parts = line.split()
    n, maximisers = int(parts[0]), parts[4:]
    got = sorted(describe(g) for g in maximisers)
    want = sorted(sorted(x) for x in EXPECTED[n])
    ok &= got == want
    print(n, "OK" if got == want else f"DIFFERENT: {got} vs {want}")
print("ALL PASS" if ok else "FAILED")
sys.exit(0 if ok else 1)
