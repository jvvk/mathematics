"""Sixteen label-disjoint 8-caterpillars perfectly embedded in the balanced tree of height 7
(Bordewich et al., Corollary 4.4 with k = 3), by the recursion of their Lemma 4.3.

Leaves are positions 0..127, left to right. A caterpillar (p0, ..., p7) needs p_s // 2**s == p0 // 2**s
and p_s // 2**(s-1) != p0 // 2**(s-1) for s = 1..7: leaf p_s hangs off the path at depth 7 - s.
"""


def build(n: int, base: int) -> list[list[int]]:
    """Lemma 4.3: a balanced tree on 2**(n-1) leaves at offset `base` embeds a(n) disjoint
    n-caterpillars; returns them as lists of positions."""
    if n == 1:
        return [[base]]
    half = 2 ** (n - 2)
    left, right = build(n - 1, base), build(n - 1, base + half)
    pow2 = (n - 1) & (n - 2) == 0  # n - 1 is a power of two
    take_l = (len(left) + 1) // 2 if pow2 else len(left)  # a(1) = 1 is the one odd case
    take = len(left) // 2 if pow2 else len(left)
    used = {p for c in left[:take_l] + right[:take] for p in c}
    free_l = [p for p in range(base, base + half) if p not in used]
    free_r = [p for p in range(base + half, base + 2 * half) if p not in used]
    out = [c + [free_r.pop(0)] for c in left[:take_l]] + [c + [free_l.pop(0)] for c in right[:take]]
    return out


def is_cat(c: list[int]) -> bool:
    return all(c[s] // 2**s == c[0] // 2**s and c[s] // 2 ** (s - 1) != c[0] // 2 ** (s - 1)
               for s in range(1, len(c)))


cats = build(8, 0)
assert len(cats) == 16 and all(len(c) == 8 and is_cat(c) for c in cats)
assert sorted(p for c in cats for p in c) == list(range(128))
print(cats)
