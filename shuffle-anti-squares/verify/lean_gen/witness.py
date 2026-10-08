"""Find (rotation, colour mask) witnesses for the tightness examples and the W_0 two-cut example."""
import sys
from functools import lru_cache
sys.setrecursionlimit(10000)


def mask_for(w: str) -> str | None:
    """Return an A/B mask making w a shuffle square, or None."""
    n = len(w)
    @lru_cache(maxsize=None)
    def go(i: int, lead: int, pend: str):
        if i == n:
            return "" if pend == "" else None
        if len(pend) > n - i:
            return None
        c = w[i]
        if pend and pend[0] == c:
            r = go(i + 1, lead, pend[1:])
            if r is not None:
                return "B" + r
        if lead < n // 2:
            r = go(i + 1, lead + 1, pend + c)
            if r is not None:
                return "A" + r
        return None
    return go(0, 0, "")


def V(K, lam, mu):
    runs = [("0", K * lam), ("1", mu), ("0", 5 * lam), ("1", 2 * mu), ("0", K * lam), ("1", mu),
            ("0", 2 * lam), ("1", mu), ("0", lam), ("1", 3 * mu)]
    return "".join(c * n for c, n in runs)


if __name__ == "__main__":
    for K, lam, mu in [(8, 1, 1), (8, 1, 3), (9, 1, 2), (9, 1, 4)]:
        w = V(K, lam, mu)
        for r in range(len(w)):
            m = mask_for(w[r:] + w[:r])
            if m:
                print(f"V {K} {lam} {mu} split={r} mask={m}")
                break
    w0 = "000010001111000011101111"
    print("W0YXZ", w0, mask_for(w0))
