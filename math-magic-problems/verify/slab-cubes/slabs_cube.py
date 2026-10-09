"""Decide whether the s-cube can be tiled with one k-slab for each k = 1..n, by going through every
combination of slab sizes whose volumes add up to s^3 (slabs.py). Resumable: progress is kept in
data/slabs_progress_N_S.json, and each call stops after BUDGET seconds.
Usage: python3 slabs_cube.py N S BUDGET [SECONDS_PER_COMBO]
"""

from __future__ import annotations

import json
import sys
import time
from pathlib import Path

from slabs import check, size_combos, solve

ROOT = Path(__file__).resolve().parent

if __name__ == "__main__":
    n, s, budget = int(sys.argv[1]), int(sys.argv[2]), float(sys.argv[3])
    per = float(sys.argv[4]) if len(sys.argv) > 4 else 20
    prog_path = ROOT / "data" / f"slabs_progress_{n}_{s}.json"
    combos = size_combos(n, s)
    prog = (
        json.loads(prog_path.read_text())
        if prog_path.exists()
        else {"done": {}, "found": None}
    )
    t0 = time.time()
    for idx, f in enumerate(combos):
        if str(idx) in prog["done"] and prog["done"][str(idx)] != "unknown":
            continue
        if prog["found"] or time.time() - t0 > budget:
            break
        st, slabs = solve(n, (s, s, s), per, faces=f)
        prog["done"][str(idx)] = st
        if slabs:
            check(n, (s, s, s), slabs)
            prog["found"] = slabs
            (ROOT / "data" / f"slabs_{n}_{s}x{s}x{s}.json").write_text(
                json.dumps({"n": n, "dims": [s, s, s], "slabs": slabs})
            )
        prog_path.write_text(json.dumps(prog))
    vals = [prog["done"].get(str(i)) for i in range(len(combos))]
    verdict = (
        "FOUND"
        if prog["found"]
        else ("impossible" if all(v == "impossible" for v in vals) else "open")
    )
    print(
        f"n={n} s={s}: {len(combos)} combos, {sum(v == 'impossible' for v in vals)} impossible, "
        f"{sum(v == 'unknown' for v in vals)} unknown, {sum(v is None for v in vals)} left -> {verdict}",
        flush=True,
    )
