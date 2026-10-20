"""Independent recheck of every finite certificate stated in paper/common-quartets.tex (gate J4).
Self-contained: imports nothing from this folder. Parses the Newick strings from the .tex itself."""

import re
from itertools import combinations, permutations
from pathlib import Path

TEX = Path(__file__).resolve().parent.parent / "paper" / "common-quartets.tex"


def parse_newick(s: str):
    s = s.replace("\\,", "").replace(" ", "")
    pos = 0

    def node():
        nonlocal pos
        if s[pos] == "(":
            pos += 1
            ch = [node()]
            while s[pos] == ",":
                pos += 1
                ch.append(node())
            assert s[pos] == ")"
            pos += 1
            return ch
        m = re.match(r"\d+", s[pos:])
        pos += len(m.group())
        return int(m.group())

    t = node()
    assert pos == len(s), s[pos:]
    return t


def leafset(t):
    return {t} if isinstance(t, int) else set().union(*map(leafset, t))


def edge_splits(t):
    """Unrooted tree given as nested lists: every subtree below the top node is one side of an edge."""
    out = []

    def rec(u, top):
        if isinstance(u, int):
            S = {u}
        else:
            S = set()
            for c in u:
                S |= rec(c, False)
        if not top:
            out.append(frozenset(S))
        return S

    rec(t, True)
    return out


def check_binary(t, n):
    def deg_ok(u, top):
        if isinstance(u, int):
            return True
        need = 3 if top else 2
        return len(u) == need and all(deg_ok(c, False) for c in u)

    assert deg_ok(t, True), "not binary"
    assert leafset(t) == set(range(n))


def displayed(splits, Q):
    res = set()
    for S in splits:
        A = S & Q
        if len(A) == 2:
            res.add(frozenset([A, frozenset(Q - A)]))
    assert len(res) == 1
    return res.pop()


def relabel(t, f):
    return f(t) if isinstance(t, int) else [relabel(c, f) for c in t]


def no_common(trees, n):
    sp = [edge_splits(t) for t in trees]
    return all(
        len({displayed(s, frozenset(Q)) for s in sp}) > 1
        for Q in combinations(range(n), 4)
    )


tex = TEX.read_text()
t13_src = re.search(r"\\bigl\((0,.*?)\\bigr\)", tex, re.DOTALL).group(1)
g = re.search(r"\\begin\{gathered\}(.*?)\\end\{gathered\}", tex, re.DOTALL).group(1)
t21_src = g.replace("\\\\", "").replace("\n", "").strip().rstrip(".")[1:-1]
T13 = parse_newick("(" + t13_src + ")")
T21 = parse_newick("(" + t21_src + ")")
check_binary(T13, 13)
check_binary(T21, 21)
trees3 = [T13, relabel(T13, lambda x: 3 * x % 13), relabel(T13, lambda x: 9 * x % 13)]
assert no_common(trees3, 13)
print("Prop 5.1: T, 3T, 9T on Z_13 share no quartet (715 quartets)")


def s4(x):
    return x if x == 0 else 4 * ((x - 1) // 4) + (x % 4) + 1


assert [s4(x) for x in range(1, 5)] == [2, 3, 4, 1]
trees4 = [T21]
for _ in range(3):
    trees4.append(relabel(trees4[-1], s4))
assert no_common(trees4, 21)
print("h(4) >= 22: T, sT, s^2T, s^3T on 21 leaves share no quartet (5985 quartets)")

# Section 5.1: the symmetric example T' and its involution; Proposition 6.1 on Z_40
tp_src = (
    re.search(r"T'=\\bigl\((.*?)\\bigr\)", tex, re.DOTALL).group(1).replace("\\,", "")
)
TP = parse_newick("(" + tp_src + ")")
check_binary(TP, 13)
assert no_common(
    [TP, relabel(TP, lambda x: 3 * x % 13), relabel(TP, lambda x: 9 * x % 13)], 13
)
inv = re.search(r"\\iota=(.*?)\\\]", tex, re.DOTALL).group(1)
iota = list(range(13))
for a, b in re.findall(r"\((\d+)\\,(\d+)\)", inv):
    iota[int(a)], iota[int(b)] = int(b), int(a)
assert all(iota[3 * x % 13] == 3 * iota[x] % 13 for x in range(13)), (
    "involution commutes with x -> 3x"
)


def splits_from0(t):
    """Edge splits, each as the side not containing leaf 0."""
    return {s if 0 not in s else frozenset(range(13)) - s for s in edge_splits(t)}


assert splits_from0(relabel(TP, iota.__getitem__)) == splits_from0(TP)
assert splits_from0(
    relabel(TP, ([0, 2, 1] + list(range(3, 13))).__getitem__)
) != splits_from0(TP), "comparison can fail"
print(
    "Sec 5.1: T', 3T', 9T' share no quartet; the involution commutes with x -> 3x and fixes T'"
)
assert [x for x in range(40) if 9 * x % 40 == x] == [0, 5, 10, 15, 20, 25, 30, 35]
print("Prop 6.2: x -> 9x fixes exactly the 8 multiples of 5 in Z_40")


# caterpillar family F_k, Definition 4.1, rebuilt from scratch
def Fk(k):
    h = 2 ** (k - 1)
    orders = [list(range(-h, h + 1))]
    for b in range(k - 1):
        posmap = {
            x: (-x if x != 0 and not ((abs(x) - 1) >> b) & 1 else x)
            for x in range(-h, h + 1)
        }
        orders.append(sorted(range(-h, h + 1), key=posmap.__getitem__))
    return orders


def cat_common(orders):
    pos = [{v: i for i, v in enumerate(o)} for o in orders]
    for Q in combinations(orders[0], 4):
        sp = set()
        for p in pos:
            s = sorted(Q, key=p.__getitem__)
            sp.add(frozenset([frozenset(s[:2]), frozenset(s[2:])]))
        if len(sp) == 1:
            return True
    return False


for k in range(1, 7):
    assert not cat_common(Fk(k)), k
print("Thm 4.2: F_k has no common quartet for k = 1..6")
# the k = 3 table printed in the paper (label at each position)
table = [
    [-4, -3, -2, -1, 0, 1, 2, 3, 4],
    [-4, 3, -2, 1, 0, -1, 2, -3, 4],
    [-4, -3, 2, 1, 0, -1, -2, 3, 4],
]
assert Fk(3) == table, Fk(3)
print("k = 3 table in the paper matches Definition 4.1")

# Snir-Yuster's k = 3 example equals F_3 up to relabelling (orders up to reversal and reordering)?
sy = [
    [1, 2, 3, 4, 5, 6, 7, 8, 9],
    [1, 2, 7, 6, 5, 4, 3, 8, 9],
    [1, 8, 3, 6, 5, 4, 7, 2, 9],
]
F = [tuple(o) for o in Fk(3)]
Fset = {frozenset([o, o[::-1]]) for o in F}
labels = list(range(-4, 5))
found = None
for perm in permutations(labels):
    f = dict(zip(range(1, 10), perm))
    img = {
        frozenset([tuple(f[x] for x in o), tuple(f[x] for x in o)[::-1]]) for o in sy
    }
    if img == Fset:
        found = perm
        break
print(
    "Snir-Yuster k=3 example equal to F_3 up to relabelling:", found is not None, found
)
