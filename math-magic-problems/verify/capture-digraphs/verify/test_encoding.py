"""Check that the Z3 attack formulas in src/realize.py agree with the square-by-square simulator in
verify/check.py on random positions, including crowded lines and diagonals. Any disagreement would
mean the solver's model of chess is wrong. Run with --mutants to confirm that broken encodings fail.

Usage: test_encoding.py [trials] [--mutants]
"""

from __future__ import annotations

import random
import sys
from pathlib import Path

from z3 import Int, IntVal, is_true, simplify, substitute

ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT / "src"))
sys.path.insert(0, str(ROOT / "verify"))
from check import capture_graph

import realize


def z3_graph(types: str, pos: list[tuple[int, int]]) -> set[tuple[int, int]]:
    n = len(pos)
    sym = [(Int(f"x{i}"), Int(f"y{i}")) for i in range(n)]
    subs = [
        (v, IntVal(c))
        for (vx, vy), (x, y) in zip(sym, pos)
        for v, c in ((vx, x), (vy, y))
    ]
    arcs = set()
    for a in range(n):
        for b in range(n):
            if a != b and is_true(
                simplify(substitute(realize.attacks(types[a], a, b, sym), *subs))
            ):
                arcs.add((a, b))
    return arcs


def trial(rng: random.Random) -> tuple[str, list[tuple[int, int]]]:
    n = rng.randint(2, 7)
    span = rng.choice([2, 3, 4, 6])
    cells = [(x, y) for x in range(span) for y in range(span)]
    pos = rng.sample(cells, min(n, len(cells)))
    types = "".join(rng.choice(realize.TYPES) for _ in pos)
    return types, pos


def run(trials: int, seed: int = 1) -> int:
    rng = random.Random(seed)
    bad = 0
    for _ in range(trials):
        types, pos = trial(rng)
        if z3_graph(types, pos) != capture_graph(types, pos):
            bad += 1
    return bad


def mutants():
    """Each mutant breaks one rule of the encoding; every one must be caught."""
    from z3 import And, Or

    orig_between, orig_attacks = realize.between, realize.attacks

    def no_antidiag(p, q, c):
        (xa, ya), (xb, yb), (xc, yc) = p, q, c
        bx = Or(And(xa < xc, xc < xb), And(xb < xc, xc < xa))
        by = Or(And(ya < yc, yc < yb), And(yb < yc, yc < ya))
        return Or(
            And(ya == yb, yc == ya, bx),
            And(xa == xb, xc == xa, by),
            And(xb - xa == yb - ya, xc - xa == yc - ya, bx),
        )

    def loose_between(p, q, c):
        (xa, ya), (xb, yb), (xc, yc) = p, q, c
        bx = Or(And(xa <= xc, xc <= xb), And(xb <= xc, xc <= xa))
        return And(ya == yb, yc == ya, bx)

    def king_as_queen(t, a, b, pos):
        return orig_attacks("Q" if t == "K" else t, a, b, pos)

    def knight_wrong(t, a, b, pos):
        return orig_attacks("K" if t == "N" else t, a, b, pos)

    def no_block(p, q, c):
        from z3 import BoolVal

        return BoolVal(False)

    cases = [
        ("between", no_antidiag),
        ("between", loose_between),
        ("between", no_block),
        ("attacks", king_as_queen),
        ("attacks", knight_wrong),
    ]
    for name, fn in cases:
        setattr(realize, name, fn)
        caught = run(300) > 0
        realize.between = orig_between
        realize.attacks = orig_attacks
        print(f"mutant {fn.__name__}: {'caught' if caught else 'SURVIVED'}")


def main() -> None:
    trials = int(next((a for a in sys.argv[1:] if a.isdigit()), 2000))
    bad = run(trials)
    print(f"{trials} random positions: {bad} disagreements")
    if "--mutants" in sys.argv:
        mutants()


if __name__ == "__main__":
    main()
