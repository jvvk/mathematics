"""Glue layouts for the 49-block inflation step.

N = 49n + r, r in [28, 76], p = n mod 2. s, t: aligned chains on [1..n], [1..n+1] from A to B[len % 2].
Block (c, which) = B(c, x): entries 49 x_i + (c if i odd else 6 - c). Layout = order + orientation of the 49 blocks
with glue numbers 1..27 interleaved, a chain from A to B[N % 2] whose junction sums are odd triangular numbers.
"""
from __future__ import annotations
import random
from aligned import odd_tri

OFFS = list(range(-21, 28))


def blocks_for(r: int, p: int) -> list[tuple[int, str]]:
    K = r - 49
    out = [(3, "t" if 3 <= K else "s")]
    for c in range(-21, 3):
        d = 6 - c
        if d <= K:
            out += [(c, "t"), (d, "t")]
        elif c <= K:
            out += [(c, "t"), (d, "s")] if p == 0 else [(c, "s"), (d, "t")]
        else:
            out += [(c, "s"), (d, "s")]
    return out


def block_ends(c: int, which: str, p: int, A: int, B: dict[int, int]) -> tuple[int, int]:
    ell_par = p if which == "s" else 1 - p          # parity of the chain length
    last_off = c if ell_par == 1 else 6 - c
    return 49 * A + c, 49 * B[ell_par] + last_off


def search(r: int, p: int, A: int, B: dict[int, int], tries: int = 400, seed: int = 0):
    """Randomised DFS over items. Returns list of ('g', v) / ('b', (c, which), reversed)."""
    N_par = (p + r) % 2
    end = B[N_par]
    blks = blocks_for(r, p)
    ends = {bk: block_ends(bk[0], bk[1], p, A, B) for bk in blks}
    glue = [g for g in range(1, 28)]
    rng = random.Random(seed)
    total = len(glue) + len(blks)

    for _ in range(tries):
        used_g = {A}; used_b = set()
        seq = [("g", A)]; tail = A
        budget = [20000]

        def free_moves(tail):
            mv = []
            for g in glue:
                if g not in used_g and odd_tri(tail + g) and (g != end or len(used_g) + len(used_b) == total - 1):
                    mv.append(("g", g, g))
            for bk in blks:
                if bk in used_b:
                    continue
                f, l = ends[bk]
                if odd_tri(tail + f):
                    mv.append(("b", (bk, False), l))
                if odd_tri(tail + l):
                    mv.append(("b", (bk, True), f))
            return mv

        def dfs(tail):
            budget[0] -= 1
            if budget[0] < 0:
                return False
            if len(used_g) + len(used_b) == total:
                return seq[-1] == ("g", end)
            mv = free_moves(tail)
            rng.shuffle(mv)
            mv.sort(key=lambda m: len(free_moves(m[2])))
            for kind, item, newtail in mv:
                if kind == "g":
                    used_g.add(item); seq.append(("g", item))
                else:
                    used_b.add(item[0]); seq.append(("b", item[0], item[1]))
                if dfs(newtail):
                    return True
                seq.pop()
                if kind == "g":
                    used_g.discard(item)
                else:
                    used_b.discard(item[0])
            return False

        if dfs(tail):
            return seq
    return None


if __name__ == "__main__":
    import sys
    A = 1; B = {0: int(sys.argv[1]), 1: int(sys.argv[2])}
    bad = []
    for p in (0, 1):
        for r in range(28, 77):
            L = search(r, p, A, B, tries=30)
            if L is None:
                bad.append((r, p))
    print("B =", B, "failed layouts:", len(bad), bad[:20])
