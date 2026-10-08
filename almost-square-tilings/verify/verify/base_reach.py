"""Which of the 151 uncovered n can one fixed squared rectangle tile at one fixed scale?

Records, for each success, the shifts (u, v) so the claim can be checked independently (Lean:
LeanProofs/AlmostSq/Counts.lean). Uses the z3 model of src/fill.py (attempt), in both orientations.
usage: base_reach.py CODE t n1 n2 ... > out.jsonl
"""
from __future__ import annotations

import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT / "src"))
from fill import decode_rect  # noqa: E402
from z3 import Distinct, Int, Or, Solver, sat  # noqa: E402


def shifts(n, t, W, H, sq, ms=4000):
    xl = sorted({x for _, x, _ in sq} | {x + s for s, x, _ in sq})
    yl = sorted({y for _, _, y in sq} | {y + s for s, _, y in sq})
    U = {X: Int(f"u{X}") for X in xl}
    V = {Y: Int(f"v{Y}") for Y in yl}
    sv = Solver()
    sv.set("timeout", ms)
    sv.add(U[0] == 0, V[0] == 0, t * W + U[W] == n + 1, t * H + V[H] == n)
    for a, b in zip(xl, xl[1:]):
        sv.add(t * (b - a) + U[b] - U[a] >= 1)
    for a, b in zip(yl, yl[1:]):
        sv.add(t * (b - a) + V[b] - V[a] >= 1)
    ks = []
    for s, x, y in sq:
        w = t * s + U[x + s] - U[x]
        h = t * s + V[y + s] - V[y]
        sv.add(Or(w - h == 1, h - w == 1))
        k = Int(f"k{len(ks)}")
        sv.add(2 * k == w + h - 1, k >= 1, k < n)
        ks.append(k)
    sv.add(Distinct(*ks))
    if sv.check() != sat:
        return None
    m = sv.model()
    return ({a: m[U[a]].as_long() for a in xl}, {b: m[V[b]].as_long() for b in yl})


def main() -> None:
    code, t, ns = sys.argv[1], int(sys.argv[2]), list(map(int, sys.argv[3:]))
    W, H, sq = decode_rect(code)
    for n in ns:
        for flip in (False, True):
            WW, HH, ss = (H, W, [(s, y, x) for s, x, y in sq]) if flip else (W, H, sq)
            r = shifts(n, t, WW, HH, ss)
            if r:
                u, v = r
                print(json.dumps({"n": n, "t": t, "flip": flip, "u": {k: x for k, x in u.items() if x},
                                  "v": {k: x for k, x in v.items() if x}}), flush=True)
                break


if __name__ == "__main__":
    main()
