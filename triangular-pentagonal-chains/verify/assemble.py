"""Build the aligned chain C_N (from 1 to b(N), b = 2 for N even, 9 for N odd) for every N >= 54:
N <= 2673 from the base file; N >= 2674 by the 49-block inflation step, using layouts.json."""
from __future__ import annotations
import gzip, json
from functools import lru_cache
from pathlib import Path

HERE = Path(__file__).parent
LAY = json.loads((HERE / "layouts.json").read_text())
A, BEND = LAY["A"], {int(k): v for k, v in LAY["B"].items()}
M0, BASE_TOP = 54, 49 * 54 + 27
_base: dict[int, list[int]] = {}


def load_base() -> None:
    with gzip.open(HERE / "base_chains.txt.gz", "rt") as f:
        for line in f:
            m, *rest = line.split()
            _base[int(m)] = [int(x) for x in rest]


def block(c: int, x: list[int]) -> list[int]:
    return [49 * v + (c if i % 2 == 0 else 6 - c) for i, v in enumerate(x)]  # i = 0 is position 1 (odd)


@lru_cache(maxsize=None)
def chain(N: int) -> tuple[int, ...]:
    if N <= BASE_TOP:
        if not _base:
            load_base()
        return tuple(_base[N])
    n, r = divmod(N - 28, 49); r += 28                 # N = 49 n + r, r in [28, 76]
    p = n % 2
    s, t = list(chain(n)), list(chain(n + 1))
    out: list[int] = []
    for item in LAY["layouts"][f"{r},{p}"]:
        if item[0] == "g":
            out.append(item[1])
        else:
            (c, which), rev = item[1], item[2]
            blk = block(c, s if which == "s" else t)
            out.extend(reversed(blk) if rev else blk)
    return tuple(out)
