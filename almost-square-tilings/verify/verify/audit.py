"""Independent audit of the whole proof certificate.

1. Every base case n in out/uncovered.txt has a tiling in out/fill/n{n}.txt that passes check.py.
2. Every residue-class record (out/cover112.jsonl, out/cover110.jsonl): the inflated dissection is
   rebuilt and cell-checked for t = t0 .. t0 + FULL - 1, and its sizes/lines are checked for
   t = t0 .. t0 + LIGHT - 1 (the certificate's affine argument covers all larger t).
3. Every n in [20, NMAX] is either a base case or n = tS + V for some record with t >= t0, where V is
   recomputed from the record's own shifts (V = v[S]) and must equal the stored value.
4. The small tilings out/small/n*.txt (n = 10, 12, 14, 15, 18) and the n = 4 tiling are admissible.
Every tiling is checked in admissible mode: pieces k x (k+1) with 1 <= k < n, all sizes distinct.
What this audit does not do: Lemma 4 (every t >= t0 works) is sampled here for LIGHT scales; its proof for all
t is in the paper and in Lean (`all_scales`).
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
        err = check(lines, n + 1, n, n)
        if err:
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
            if r["V"] != v[S]:
                print(f"CLASS S={S}: stored V={r['V']} but v[S]={v[S]}")
                bad += 1
                continue
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
                err = check(lines, n + 1, n, n)
                if err:
                    print(f"CLASS S={S} V={v[S]} t={t}: {err}")
                    bad += 1
            recs.append((S, v[S], r["t0"]))
    print(f"classes: {len(recs)} checked")
    small = {4: ["SOL", "3 3 4 0 0", "2 2 3 3 0", "1 2 1 3 3"]}  # the n = 4 tiling of Section 1
    for n in (10, 12, 14, 15, 18):
        f = ROOT / "out" / "small" / f"n{n}.txt"
        small[n] = [ln for ln in f.read_text().splitlines() if ln.strip() and not ln.startswith("COUNT")]
    for n, lines in small.items():
        err = check(lines, n + 1, n, n)
        if err:
            print(f"SMALL n={n}: {err}")
            bad += 1
    print(f"small tilings: {len(small)} checked (n = {sorted(small)})")
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
    ok = bad == 0 and not gaps and len(even) == 56 and len(odd) == 55
    print("AUDIT PASS" if ok else f"AUDIT FAIL ({bad})")
    if not ok:
        sys.exit(1)


if __name__ == "__main__":
    main()
