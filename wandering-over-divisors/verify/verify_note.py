"""Independent check of every finite statement in the note "Wandering over the divisors of a power of ten".

Shares no code with the C solver (solve.c). Written from the rules alone: board {0..n}^2, moves
E = (1,0), N = (0,1), D = (-1,-1), no square named twice, the player to move with no move loses.

Checks, for n = 1..NMAX (default 8, i.e. boards up to 9x9):
  Theorem 1  losing-square counts 4, 9, 20, 31 for n = 2, 4, 6, 8; the listed exceptions; 29/49.
  Theorem 3  from (k,k), k < n, the openings E and N lose.
  Theorem 5  from (a,0), 1 <= a <= n, n >= 2, the opening N loses; fails for n = 1 as stated.
  Theorem 7  (n,0), (0,n), (2,0) losing for n >= 2; (2,2) losing for n >= 3.
  Conjecture 8 (odd n) agrees with the exact solution; its count is 3m^2 - 4m + 5 (m >= 2), m up to 200.
  Section 8  the copying line on the 3x3 board loses for Bob.
Then plants wrong statements (mutants) and confirms each is rejected.
"""

from __future__ import annotations

import sys
from fractions import Fraction
from pathlib import Path
from functools import cache

MOVES = ((1, 0), (0, 1), (-1, -1))


class Board:
    def __init__(self, n: int) -> None:
        self.n = n
        self.side = n + 1

    def idx(self, x: int, y: int) -> int:
        return y * self.side + x

    def nbrs(self, i: int) -> list[int]:
        x, y = i % self.side, i // self.side
        out = []
        for dx, dy in MOVES:
            u, v = x + dx, y + dy
            if 0 <= u <= self.n and 0 <= v <= self.n:
                out.append(self.idx(u, v))
        return out

    def solver(self):
        nb = [self.nbrs(i) for i in range(self.side * self.side)]

        def reach(pos: int, used: int) -> int:
            seen, stack = 0, [pos]
            while stack:
                p = stack.pop()
                for q in nb[p]:
                    bit = 1 << q
                    if not used & bit and not seen & bit:
                        seen |= bit
                        stack.append(q)
            return seen

        @cache
        def mover_wins_key(pos: int, free: int) -> bool:
            for q in nb[pos]:
                if free >> q & 1:
                    # after moving to q, the future depends on cells reachable from q avoiding used ones
                    rest = free & ~(1 << q)
                    used = ~rest
                    if not mover_wins_key(q, reach(q, used) & rest):
                        return True
            return False

        def mover_wins(pos: int, used: int) -> bool:
            return mover_wins_key(pos, reach(pos, used) & ~used)

        return mover_wins


def losing_set(n: int) -> set[tuple[int, int]]:
    b = Board(n)
    win = b.solver()
    return {
        (x, y)
        for x in range(n + 1)
        for y in range(n + 1)
        if not win(b.idx(x, y), 1 << b.idx(x, y))
    }


def opening_loses(n: int, start: tuple[int, int], step: tuple[int, int]) -> bool | None:
    """True if Alice's first move `step` from `start` loses for her (Bob, now to move, wins)."""
    b = Board(n)
    win = b.solver()
    x, y = start
    u, v = x + step[0], y + step[1]
    if not (0 <= u <= n and 0 <= v <= n):
        return None
    used = (1 << b.idx(x, y)) | (1 << b.idx(u, v))
    return win(b.idx(u, v), used)


def conjecture_even(n: int, x: int, y: int) -> bool:
    """Conjecture 8 (n odd): True if (x, y) is losing."""
    if x < y:
        x, y = y, x
    if x == y:
        return y % 2 == 0 or y == n
    if y == 1:
        return x == n
    if y % 2 == 0:
        return y < n and x >= y + 2
    return (x - y) % 2 == 0


def conj_count(n: int) -> int:
    return sum(conjecture_even(n, x, y) for x in range(n + 1) for y in range(n + 1))


def run(nmax: int) -> dict:
    res: dict = {"L": {}, "T3": True, "T4": True, "T6": True, "conj": {}}
    for n in range(1, nmax + 1):
        Ls = losing_set(n)
        res["L"][n] = Ls
        for k in range(n):
            for step in ((1, 0), (0, 1)):
                if opening_loses(n, (k, k), step) is not True:
                    res["T3"] = False
        if n >= 2:
            for a in range(1, n + 1):
                if opening_loses(n, (a, 0), (0, 1)) is not True:
                    res["T4"] = False
            if not {(n, 0), (0, n), (2, 0)} <= Ls:
                res["T6"] = False
        if n >= 3 and (2, 2) not in Ls:
            res["T6"] = False
        if n % 2 == 1:
            pred = {
                (x, y)
                for x in range(n + 1)
                for y in range(n + 1)
                if conjecture_even(n, x, y)
            }
            res["conj"][n] = pred == Ls
        print(f"  n={n}: {len(Ls)} losing squares", flush=True)
    return res


def copying_line_loses() -> bool:
    """3x3 from (2,0): N, N, D, D, then Alice E; Bob must have no move."""
    b = Board(2)
    path = [(2, 0), (2, 1), (2, 2), (1, 1), (0, 0), (1, 0)]
    used = {b.idx(*p) for p in path}
    last = b.idx(1, 0)
    return all(q in used for q in b.nbrs(last))


def main() -> int:
    nmax = int(sys.argv[1]) if len(sys.argv) > 1 else 8
    print(f"solving boards n = 1..{nmax}")
    r = run(nmax)
    L = r["L"]
    checks = []
    counts = {n: len(L[n]) for n in L}
    checks.append(
        (
            "Thm 1 counts 4, 9, 20, 31",
            [counts.get(n) for n in (2, 4, 6, 8) if n in counts]
            == [4, 9, 20, 31][: len([n for n in (2, 4, 6, 8) if n in counts])],
        )
    )
    ee = lambda n: {(x, y) for x in range(0, n + 1, 2) for y in range(0, n + 1, 2)}
    if 6 in L:
        checks.append(
            ("Thm 1 exceptions n=6", L[6] - ee(6) == {(4, 3), (6, 3), (3, 4), (3, 6)})
        )
        checks.append(
            (
                "Thm 1 probability 29/49",
                Fraction(49 - len(L[6]), 49) == Fraction(29, 49),
            )
        )
    if 8 in L:
        checks.append(
            (
                "Thm 1 exceptions n=8",
                L[8] - ee(8) == {(5, 4), (8, 3), (8, 5), (4, 5), (3, 8), (5, 8)},
            )
        )
    checks.append(("Thm 1 no EE square winning", all(ee(n) <= L[n] for n in L)))
    checks.append(("Thm 3 diagonal openings", r["T3"]))
    checks.append(("Thm 5 bottom row N opening", r["T4"]))
    checks.append(
        (
            "Thm 5 bound n >= 2 needed (n=1 fails)",
            opening_loses(1, (1, 0), (0, 1)) is False,
        )
    )
    checks.append(("Thm 7 corners, (2,0), (2,2)", r["T6"]))
    checks.append(
        (
            "Thm 7 bound: corner (0,1) is winning when n=1",
            (0, 1) not in L[1],
        )
    )
    checks.append(("Conj 8 agrees on odd n", all(r["conj"].values())))
    checks.append(
        (
            "Conj 8 count 3m^2-4m+5, m=2..200",
            all(conj_count(2 * m - 1) == 3 * m * m - 4 * m + 5 for m in range(2, 201)),
        )
    )
    checks.append(("Sec 8 copying line loses on 3x3", copying_line_loses()))
    checks.append(
        ("3x3: only the corners are losing", L[2] == {(0, 0), (2, 0), (0, 2), (2, 2)})
    )
    tables = Path(__file__).resolve().parent / "data"
    agree = []
    for n in L:
        f = tables / f"sq{n + 1}.txt"
        if f.exists():
            rows = f.read_text().split()
            c_L = {
                (x, y)
                for y in range(n + 1)
                for x in range(n + 1)
                if rows[n - y][x] == "L"
            }
            agree.append(c_L == L[n])
    checks.append(
        (
            f"agrees square by square with the C tables ({len(agree)} boards)",
            bool(agree) and all(agree),
        )
    )
    ok = True
    for name, val in checks:
        print(f"{'PASS' if val else 'FAIL'}  {name}")
        ok &= bool(val)

    # mutants: each wrong statement must be rejected
    mutants = [
        ("count for n=6 is 16 (naive answer)", len(L.get(6, set())) == 16),
        (
            "(2,2) winning when n=2",
            (2, 2) not in L[2],
        ),
        ("Thm 5 also for n=1", opening_loses(1, (1, 0), (0, 1)) is True),
        (
            "Thm 3 also with D opening from (1,1), n=4",
            opening_loses(4, (1, 1), (-1, -1)) is True,
        ),
        (
            "Conj 8 with x >= y+1 on even rows",
            all(
                {
                    (x, y)
                    for x in range(n + 1)
                    for y in range(n + 1)
                    if (
                        lambda a, b: (
                            (a == b and (b % 2 == 0 or b == n))
                            or (b % 2 == 0 and b < n and a >= b + 1)
                            or (b == 1 and a == n)
                            or (b >= 3 and b % 2 == 1 and a > b and (a - b) % 2 == 0)
                        )
                    )(max(x, y), min(x, y))
                }
                == L[n]
                for n in L
                if n % 2 == 1
            ),
        ),
        (
            "count formula 3m^2-4m+4",
            all(conj_count(2 * m - 1) == 3 * m * m - 4 * m + 4 for m in range(2, 50)),
        ),
        ("diagonal (3,3) losing for n=6", (3, 3) in L.get(6, {(3, 3)}) and 6 in L),
    ]
    for name, val in mutants:
        print(f"{'mutant SURVIVED' if val else 'mutant killed  '}  {name}")
        ok &= not val
    print("ALL PASS" if ok else "FAILURES")
    return 0 if ok else 1


if __name__ == "__main__":
    sys.exit(main())
