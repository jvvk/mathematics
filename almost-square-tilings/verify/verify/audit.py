"""Independent audit of the whole proof certificate.

1. Every base case n in out/uncovered.txt has a tiling in out/fill/n{n}.txt that passes check.py.
2. Every residue-class record (out/cover112.jsonl, out/cover110.jsonl): the inflated dissection is
   rebuilt and cell-checked for t = t0 .. t0 + FULL - 1, and its sizes/lines are checked for
   t = t0 .. t0 + LIGHT - 1 (the certificate's affine argument covers all larger t).
3. Every n in [20, NMAX] is either a base case or n = tS + V for some record with t >= t0.
"""

from __future__ import annotations

import json
import sys
from pathlib import Path

ROOT = Path(sys.argv[1]).resolve() if len(sys.argv) > 1 else Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT / "verify"))
from check import check

FULL, LIGHT, NMAX = 2, 300, 20000


def squares_of(S: int) -> list[tuple[int, int, int]]:
    lines = (ROOT / "out" / f"sq{S}.txt").read_text().splitlines()
    return [tuple(map(int, ln.split())) for ln in lines[1:] if ln.strip()]


def inflate(sq, u, v, t):
    X = lambda a: t * a + u[a]
    Y = lambda b: t * b + v[b]
    return [(X(x + s) - X(x), Y(y + s) - Y(y), X(x), Y(y)) for s, x, y in sq]


def light_ok(S, sq, u, v, t) -> bool:
    xs, ys = sorted(u), sorted(v)
    if any(t * b + u[b] <= t * a + u[a] for a, b in zip(xs, xs[1:])):
        return False
    if any(t * b + v[b] <= t * a + v[a] for a, b in zip(ys, ys[1:])):
        return False
    n = t * S + v[S]
    if t * S + u[S] != n + 1:
        return False
    sizes = []
    for w, h, _, _ in inflate(sq, u, v, t):
        if abs(w - h) != 1:
            return False
        sizes.append(min(w, h))
    return min(sizes) >= 1 and max(sizes) < n and len(set(sizes)) == len(sizes)


def main() -> None:
    bad = 0
    base = [int(x) for x in (ROOT / "out" / "uncovered.txt").read_text().split()]
    for n in base:
        f = ROOT / "out" / "fill" / f"n{n}.txt"
        lines = [
            ln
            for ln in f.read_text().splitlines()
            if ln.strip() and not ln.startswith("COUNT")
        ]
        err = check(lines, n + 1, n)
        sizes = [int(ln.split()[0]) for ln in lines if ln != "SOL"]
        if err or max(sizes) >= n:
            print(f"BASE n={n}: {err}")
            bad += 1
    print(f"base cases: {len(base)} checked")
    recs = []
    for S in (112, 110):
        sq = squares_of(S)
        for ln in (ROOT / "out" / f"cover{S}.jsonl").read_text().splitlines():
            r = json.loads(ln)
            if not r["t0"]:
                continue
            u = {int(k): x for k, x in r["u"].items()}
            v = {int(k): x for k, x in r["v"].items()}
            for t in range(r["t0"], r["t0"] + LIGHT):
                if not light_ok(S, sq, u, v, t):
                    print(f"CLASS S={S} V={r['V']} fails at t={t}")
                    bad += 1
                    break
            for t in range(r["t0"], r["t0"] + FULL):
                n = t * S + v[S]
                lines = ["SOL"] + [
                    f"{min(w, h)} {w} {h} {x} {y}"
                    for w, h, x, y in inflate(sq, u, v, t)
                ]
                err = check(lines, n + 1, n)
                if err:
                    print(f"CLASS S={S} V={r['V']} t={t}: {err}")
                    bad += 1
            recs.append((S, r["V"], r["t0"]))
    print(f"classes: {len(recs)} checked")
    baseset = set(base)
    gaps = [
        n
        for n in range(20, NMAX + 1)
        if n not in baseset
        and not any((n - V) % S == 0 and (n - V) // S >= t0 for S, V, t0 in recs)
    ]
    print(
        f"uncovered n in [20, {NMAX}]: {gaps[:20]}{'...' if len(gaps) > 20 else ''} ({len(gaps)})"
    )
    even = {V % 112 for S, V, _ in recs if S == 112}
    odd = {V % 110 for S, V, _ in recs if S == 110}
    print(f"residues: even mod 112 {len(even)}/56, odd mod 110 {len(odd)}/55")
    print(
        "AUDIT PASS"
        if bad == 0 and not gaps and len(even) == 56 and len(odd) == 55
        else f"AUDIT FAIL ({bad})"
    )


if __name__ == "__main__":
    main()
