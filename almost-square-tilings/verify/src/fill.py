"""Tile specific R_n by inflating any dissection of a rectangle into squares, at a fixed scale t.

Base: a W x H rectangle cut into squares (from perfect squared squares or perfect squared rectangles,
either orientation). At scale t with integer line shifts u, v (u(0) = v(0) = 0) the square i becomes a
(t s_i + du_i) x (t s_i + dv_i) rectangle. Constraints: du_i - dv_i = +-1 (almost-square), container
t W + u(W) = n + 1 and t H + v(H) = n, cut lines strictly increasing, sizes (w + h - 1)/2 >= 1, all
distinct and < n. Results (verified with verify/check.py) go to out/fill/n{n}.txt; a log line per n.

Usage: fill.py n1 n2 ... [--budget 100]
"""

from __future__ import annotations

import argparse
import re
import subprocess
import sys
import time
from pathlib import Path

from z3 import Distinct, Int, Or, Solver, sat

ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT / "src"))


def load_bases() -> list[tuple[int, int, list[tuple[int, int, int]]]]:
    """(W, H, squares) for every catalogue dissection, both orientations, near-square first."""
    bases = []
    codes = []
    for f in sorted((ROOT / "ref").glob("bk2*.txt")):
        codes += [c for c in f.read_text().split() if c.startswith("(")]
    for ln in (ROOT / "ref" / "spsr16.txt").read_text().splitlines():
        m = re.search(r"(\(.*\))", ln)
        if m:
            codes.append(m.group(1))
    for code in codes:
        try:
            W, H, sq = decode_rect(code)
        except ValueError:
            continue
        bases.append((W, H, sq))
        bases.append((H, W, [(s, y, x) for s, x, y in sq]))
    return bases


def decode_rect(code: str) -> tuple[int, int, list[tuple[int, int, int]]]:
    groups = [list(map(int, g.split(","))) for g in re.findall(r"\(([^)]*)\)", code)]
    W = sum(groups[0])
    area = sum(s * s for g in groups for s in g)
    if area % W:
        raise ValueError("not a rectangle")
    H = area // W
    depth = [0] * W
    placed = []
    for g in groups:
        d = min(depth)
        x = depth.index(d)
        for s in g:
            if any(depth[c] != d for c in range(x, x + s)):
                raise ValueError("bad code")
            placed.append((s, x, d))
            for c in range(x, x + s):
                depth[c] += s
            x += s
    if any(v != H for v in depth):
        raise ValueError("not full")
    return W, H, [(s, x, H - top - s) for s, x, top in placed]


def attempt(
    n: int, t: int, W: int, H: int, sq: list[tuple[int, int, int]], ms: int
) -> list[str] | None:
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
    sizes = []
    for s, x, y in sq:
        w = t * s + U[x + s] - U[x]
        h = t * s + V[y + s] - V[y]
        sv.add(Or(w - h == 1, h - w == 1))
        k = Int(f"k{len(sizes)}")
        sv.add(2 * k == w + h - 1, k >= 1, k < n)
        sizes.append(k)
    sv.add(Distinct(*sizes))
    if sv.check() != sat:
        return None
    m = sv.model()
    X = lambda a: t * a + m[U[a]].as_long()
    Y = lambda b: t * b + m[V[b]].as_long()
    out = ["SOL"]
    for s, x, y in sq:
        w, h = X(x + s) - X(x), Y(y + s) - Y(y)
        out.append(f"{min(w, h)} {w} {h} {X(x)} {Y(y)}")
    return out


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("ns", type=int, nargs="+")
    ap.add_argument("--budget", type=float, default=100)
    ap.add_argument(
        "--slack", type=int, default=10, help="max |t*W - (n+1)| and |t*H - n|"
    )
    ap.add_argument("--ms", type=int, default=3000)
    ap.add_argument("--tmax", type=int, default=7)
    a = ap.parse_args()
    bases = load_bases()
    outdir = ROOT / "out" / "fill"
    outdir.mkdir(exist_ok=True)
    t0 = time.time()
    for n in a.ns:
        if (outdir / f"n{n}.txt").exists():
            continue
        cands = []
        for W, H, sq in bases:
            for t in range(1, a.tmax + 1):
                dw, dh = abs(t * W - (n + 1)), abs(t * H - n)
                if dw <= a.slack and dh <= a.slack:
                    cands.append((dw + dh, len(sq), t, W, H, sq))
        cands.sort(key=lambda c: (c[0], c[1]))
        found = False
        for _, _, t, W, H, sq in cands:
            if time.time() - t0 > a.budget:
                print(f"n={n}: budget spent", flush=True)
                return
            sol = attempt(n, t, W, H, sq, a.ms)
            if sol:
                f = outdir / f"n{n}.txt"
                f.write_text("\n".join(sol) + "\n")
                chk = subprocess.run(
                    [
                        sys.executable,
                        str(ROOT / "verify" / "check.py"),
                        str(f),
                        str(n + 1),
                        str(n),
                    ],
                    capture_output=True,
                    text=True,
                ).stdout.strip()
                print(f"n={n}: base {W}x{H} ({len(sq)} sq) t={t}: {chk}", flush=True)
                if not chk.startswith("VALID"):
                    f.unlink()
                    continue
                found = True
                break
        if not found:
            print(f"n={n}: no base worked ({len(cands)} tried)", flush=True)


if __name__ == "__main__":
    main()
