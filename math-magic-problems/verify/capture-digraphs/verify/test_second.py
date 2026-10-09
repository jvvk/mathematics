"""verify/second.py must accept every real position: fix random types and squares, demand exactly
their simulated capture graph, and the cvc5 model must be SAT. Mutants that drop a direction or
ignore blocking must be caught."""

from __future__ import annotations

import random
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
import second  # noqa: E402
from check import capture_graph  # noqa: E402
from cvc5.pythonic import Int, Not, Solver, sat  # noqa: E402


def accepts(types: str, pos: list[tuple[int, int]]) -> bool:
    n = len(pos)
    arcs = capture_graph(types, pos)
    P = [(Int(f"x{i}"), Int(f"y{i}")) for i in range(n)]
    T = [Int(f"t{i}") for i in range(n)]
    s = Solver()
    for i in range(n):
        s.add(P[i][0] == pos[i][0], P[i][1] == pos[i][1], T[i] == "KQRBN".index(types[i]))
    for a in range(n):
        for b in range(n):
            if a != b:
                e = second.attack(P, T, a, b)
                s.add(e if (a, b) in arcs else Not(e))
    return s.check() == sat


def run(trials: int, seed: int = 3) -> int:
    rng = random.Random(seed)
    bad = 0
    for _ in range(trials):
        n = rng.randint(2, 6)
        span = rng.choice([2, 3, 4, 5])
        pos = rng.sample([(x, y) for x in range(span) for y in range(span)], min(n, span * span))
        types = "".join(rng.choice("KQRBN") for _ in pos)
        bad += not accepts(types, pos)
    return bad


if __name__ == "__main__":
    trials = int(sys.argv[1]) if len(sys.argv) > 1 else 400
    print(f"{trials} random positions rejected: {run(trials)}")
    orig_orth, orig_ray = list(second.ORTH), second.ray_attack
    second.ORTH = orig_orth[:3]
    print("mutant missing rook direction caught:", run(200) > 0)
    second.ORTH = orig_orth
    second.ray_attack = lambda pos, a, b, d: second.on_ray(pos[a], pos[b], d, 0, None)[1]
    print("mutant no blocking caught:", run(200) > 0)
    second.ray_attack = orig_ray
