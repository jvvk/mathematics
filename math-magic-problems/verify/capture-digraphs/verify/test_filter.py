"""The pruning rule realize.plausible must never reject a real position: for random positions, the
piece types together with their own capture graph must pass. A deliberately wrong rule must fail."""

from __future__ import annotations

import random
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT / "src"))
sys.path.insert(0, str(ROOT / "verify"))
import realize  # noqa: E402
from check import capture_graph  # noqa: E402


def run(plausible, trials: int = 200_000, seed: int = 2) -> int:
    rng = random.Random(seed)
    bad = 0
    for _ in range(trials):
        n = rng.randint(2, 7)
        span = rng.choice([2, 3, 4, 5])
        cells = [(x, y) for x in range(span) for y in range(span)]
        pos = rng.sample(cells, min(n, len(cells)))
        types = "".join(rng.choice(realize.TYPES) for _ in pos)
        if not plausible(types, capture_graph(types, pos), len(pos)):
            bad += 1
    return bad


def too_strict(types, arcs, n):
    """Mutant: also forbids a one-way attack from a king to a rook, which is possible diagonally."""
    if any((a, b) in arcs and (b, a) not in arcs and types[a] == "K" and types[b] == "R"
           for a in range(n) for b in range(n) if a != b):
        return False
    return realize.plausible(types, arcs, n)


if __name__ == "__main__":
    print("plausible rejections of real positions:", run(realize.plausible))
    print("mutant too_strict caught:", run(too_strict, 20_000) > 0)
