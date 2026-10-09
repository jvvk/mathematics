"""Armies of bishops (Friedman, Math Magic, March 2005): verify B(3,5)=5 and B(3,6)=8.

Lower bounds: the two positions below are checked with a direct move simulator.
Upper bounds: exhaustive count over colourings of diagonals (no solver), using
  (i) bishops on one diagonal see each other in a chain, so an occupied diagonal is one colour;
  (ii) if every diagonal is one colour, no bishop attacks another colour;
  (iii) light and dark squares share no diagonal, so they can be counted separately.
Run: python3 check.py   (standard library only, about a minute)
"""
from itertools import product


def attacks_ok(board: dict[tuple[int, int], int], N: int) -> bool:
    for (x, y), c in board.items():
        for dx, dy in ((1, 1), (1, -1), (-1, 1), (-1, -1)):
            u, v = x + dx, y + dy
            while 0 <= u < N and 0 <= v < N:
                if (u, v) in board:
                    if board[(u, v)] != c:
                        return False
                    break
                u += dx; v += dy
    return True

def counts(board): 
    out = [0, 0, 0]
    for c in board.values(): out[c - 1] += 1
    return out

def vectors(N: int, parity: int, C: int = 3) -> set[tuple[int, ...]]:
    cells = [(x, y) for x in range(N) for y in range(N) if (x + y) % 2 == parity]
    s = sorted({x + y for x, y in cells}); d = sorted({x - y for x, y in cells})
    cl = [(s.index(x + y), len(s) + d.index(x - y)) for x, y in cells]
    out = set()
    for a in product(range(C + 1), repeat=len(s) + len(d)):   # 0 = diagonal unused
        v = [0] * (C + 1)
        for p, q in cl:
            if a[p] == a[q]:
                v[a[p]] += 1
        out.add(tuple(v[1:]))
    return out

def B(N: int, C: int = 3) -> int:
    A, D = vectors(N, 0, C), vectors(N, 1, C)
    return max(min(a[i] + b[i] for i in range(C)) for a in A for b in D)

if __name__ == "__main__":
    import json, sys
    pos = json.load(open("positions.json"))
    for key, N, k in (("5", 5, 5), ("6", 6, 8)):
        board = {(x, y): c for x, y, c in pos[key]}
        print(f"{N}x{N}: counts {counts(board)}, no cross-colour attack: {attacks_ok(board, N)}")
        assert counts(board) == [k] * 3 and attacks_ok(board, N)
    for N in (3, 4, 5, 6):
        print(f"B(3,{N}) = {B(N)}")
