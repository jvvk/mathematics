"""Independent check of a network hit: square sides from the potentials, area identity, then an explicit
placement by exhaustive bottom-left fill (exact integer geometry, no network theory)."""
import sys
from collections import Counter

def sides(edges, pot):
    out = []
    for e in edges:
        a, b = map(int, e.rstrip("*").split("-"))
        if e.endswith("*"):
            continue
        out.append(abs(pot[a] - pot[b]))
    return out

def place(W, H, multiset):
    """Exhaustive bottom-left-fill search: can these squares tile W x H exactly? Returns placements or None."""
    sky = [0] * W  # skyline heights
    rem = Counter(multiset)
    placed = []
    def rec():
        if not rem:
            return all(h == H for h in sky)
        lo = min(sky); x = sky.index(lo)
        run = 0
        while x + run < W and sky[x + run] == lo: run += 1
        for s in sorted(rem, reverse=True):
            if s <= run and lo + s <= H and rem[s]:
                rem[s] -= 1
                if rem[s] == 0: del rem[s]
                for i in range(x, x + s): sky[i] += s
                placed.append((x, lo, s))
                if rec(): return True
                placed.pop()
                for i in range(x, x + s): sky[i] -= s
                rem[s] += 1
        return False
    return placed if rec() else None

if __name__ == "__main__":
    line = sys.argv[1]
    edges = line.split("edges:")[1].split("potentials:")[0].split()
    pot = list(map(int, line.split("potentials:")[1].split()))
    S = sides(edges, pot)
    W, H = map(int, line.split()[2].split("x"))
    print("squares:", len(S), sorted(S, reverse=True))
    print("area check:", sum(s * s for s in S), "vs", W * H, "->", sum(s * s for s in S) == W * H)
    P = place(W, H, S)
    print("explicit tiling found:", P is not None)
    if P: print("placements (x, y, side):", P)
