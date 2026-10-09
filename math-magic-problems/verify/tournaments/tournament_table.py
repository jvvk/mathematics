"""Compare tournament.py optima with Friedman's published tables (data/tournament_published.json).
Usage: python3 tournament_table.py rank|winner KMAX NMAX"""
from __future__ import annotations

import json
import sys
import time
from fractions import Fraction
from pathlib import Path

from tournament import solve

PUB = json.loads((Path(__file__).resolve().parent / "data" / "tournament_published.json").read_text())

if __name__ == "__main__":
    mode, kmax, nmax = sys.argv[1], int(sys.argv[2]), int(sys.argv[3])
    for k in range(2, kmax + 1):
        for n in range(nmax + 1):
            if n >= len(PUB[mode].get(str(k), [])):
                break
            t = time.time()
            f = solve(mode, k, n)
            p = PUB[mode].get(str(k), [None] * 8)[n]
            flag = "" if p is None else ("ok" if Fraction(p) == f else f"DIFFERS from published {p}")
            print(f"{mode} K={k} N={n}: {f} ({float(f):.4%}) {flag} [{time.time() - t:.1f}s]", flush=True)
