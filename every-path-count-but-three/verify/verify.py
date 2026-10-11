"""Exact proof check that f(G_a) = s*a + r for EVERY a >= 1.

G_a = H + a new vertices, each adjacent exactly to x and y.
Lemma (STATUS.md): for endpoints u, v the number of u-v simple paths is A + B*t, t = number of new vertices other
than u, v (a path passes x and y once each, so it has at most one interior new vertex, and interior new vertices are
interchangeable). Endpoint types: (h, h'), (h, new), (new, new); by symmetry all new vertices are alike.
We read A, B off two values of a, then compare affine functions for all a >= 1.
"""
from fractions import Fraction
import networkx as nx
from family import grow
from paths import pair_counts


def affine_forms(H: nx.Graph, x, y) -> dict[tuple, tuple[int, int, int]]:
    """type -> (A, B, k) with count = A + B*(a - k), k = number of new endpoints; type exists iff a >= max(k, 1)."""
    n0 = max(H.nodes()) + 1
    forms: dict[tuple, tuple[int, int, int]] = {}
    pcs = {a: pair_counts(grow(H, x, y, a)) for a in (2, 3, 4)}
    hv = sorted(H.nodes())
    types = [((u, v), (u, v), 0) for i, u in enumerate(hv) for v in hv[i + 1:]]
    types += [((u, "new"), (min(u, n0), max(u, n0)), 1) for u in hv]
    types += [(("new", "new"), (n0, n0 + 1), 2)]
    for name, pair, k in types:
        c = [pcs[a].get(pair, 0) for a in (2, 3, 4)]
        A, B = c[0] - B_of(c) * (2 - k), B_of(c)
        assert c[2] - c[1] == B, (name, c)  # affine check, a redundant third point
        forms[name] = (A, B, k)
    return forms


def B_of(c: list[int]) -> int:
    return c[1] - c[0]


def prove(H: nx.Graph, x, y, s: int, r: int) -> str:
    forms = affine_forms(H, x, y)
    # value at a: A + B*(a-k) = B*a + (A - B*k)
    lines = {t: (B, A - B * k, max(k, 1)) for t, (A, B, k) in forms.items()}
    hit = [t for t, (sl, ic, _) in lines.items() if sl == s and ic == r]
    assert hit, "no pair type attains s*a + r"
    for t, (sl, ic, amin) in lines.items():
        # need sl*a + ic <= s*a + r for all a >= amin (and the attaining type exists for a >= 1)
        assert sl <= s and sl * amin + ic <= s * amin + r, (t, sl, ic)
    assert any(lines[t][2] == 1 for t in hit), "attaining type must exist at a = 1"
    # direct cross-check against brute force for a = 1..9
    from paths import f
    for a in range(1, 10):
        assert f(grow(H, x, y, a))[0] == s * a + r, a
    return f"PROVED f(G_a) = {s}a + {r} for all a >= 1; attained by {hit}"


FAMILIES = {
    "4a+3": ([(0, 1), (0, 3), (0, 4), (1, 2), (2, 3), (3, 4)], 1, 4, 4, 3),
    "6a+1": ([(0, 1), (1, 2), (1, 3), (1, 4), (2, 3), (2, 4)], 0, 3, 6, 1),
    "6a+9": ([(0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (1, 2), (2, 3), (2, 5), (3, 4)], 2, 4, 6, 9),
    "6a+11": ([(0, 1), (0, 3), (0, 4), (0, 5), (1, 2), (1, 5), (2, 3), (2, 5), (3, 4)], 0, 2, 6, 11),
    # K_{2,a+1}: H = path x-m-y, f = 2(a+1) - 2 = 2a
    "2a": ([(0, 1), (1, 2)], 0, 2, 2, 0),
}

if __name__ == "__main__":
    for name, spec in FAMILIES.items():
        E, x, y, s, r = spec
        print(name, "->", prove(nx.Graph(E), x, y, s, r))
