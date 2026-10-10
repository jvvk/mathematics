"""Independent plain brute force for the {SW, N, E} piece game: no table, no shortcuts.

Same output convention as solve.c: rows from y = R-1 down to 0, 'L' = player to move loses.
Only for small boards (R*C <= 30 or so).
"""

import sys
from functools import cache

MOVES: tuple[tuple[int, int], ...] = ((-1, -1), (0, 1), (1, 0))


def board(r: int, c: int) -> list[str]:
    @cache
    def wins(pos: tuple[int, int], visited: frozenset[tuple[int, int]]) -> bool:
        x, y = pos
        for dx, dy in MOVES:
            q = (x + dx, y + dy)
            if 0 <= q[0] < c and 0 <= q[1] < r and q not in visited:
                if not wins(q, visited | {q}):
                    return True
        return False

    return [
        "".join("W" if wins((x, y), frozenset({(x, y)})) else "L" for x in range(c))
        for y in range(r - 1, -1, -1)
    ]


if __name__ == "__main__":
    r, c = int(sys.argv[1]), int(sys.argv[2])
    print("\n".join(board(r, c)))
