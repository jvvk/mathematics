"""Assert every number the note quotes from the exhaustive search, then reject deliberate mutants.

Compiles tilesq.c into a temporary directory, runs it for n = 1..14 (all eight orientations), and checks:
the free n-omino counts against OEIS A000105, the number of n-ominoes tiling the n x n square, and that for
each prime n the single tiling n-omino is the straight bar. A translations-only build must change the
composite counts, so the search is not passing vacuously.

    timeout 300 nice -n 15 ~/.venvs/main/bin/python check.py
"""

from __future__ import annotations

import re
import subprocess
import sys
import tempfile
from pathlib import Path

HERE = Path(__file__).resolve().parent
NMAX = 14
A000105 = [1, 1, 2, 5, 12, 35, 108, 369, 1285, 4655, 17073, 63600, 238591, 901971]
COMPOSITE = {
    4: 4,
    6: 4,
    8: 10,
    9: 2,
    10: 6,
    12: 55,
    14: 8,
}  # quoted in the note's search sentence
PRIMES = [2, 3, 5, 7, 11, 13]
TRANSLATION_ONLY = {
    4: 2,
    6: 2,
    8: 2,
    10: 2,
}  # the translations-only control from STATUS.md


def run(
    binary: Path, n: int, mutant: bool = False
) -> tuple[int, int, list[list[tuple[int, int]]]]:
    args = [str(binary), str(n)] + (["mut"] if mutant else [])
    out = subprocess.run(
        args, capture_output=True, text=True, check=True, timeout=120
    ).stdout
    m = re.search(r"SUMMARY n=(\d+) free=(\d+) tiling=(\d+)", out)
    assert m and int(m[1]) == n
    tiles = [
        [(int(a), int(b)) for a, b in re.findall(r"\((-?\d+),(-?\d+)\)", line)]
        for line in out.splitlines()
        if line.startswith("TILES:")
    ]
    return int(m[2]), int(m[3]), tiles


def is_bar(cells: list[tuple[int, int]]) -> bool:
    xs, ys = {c[0] for c in cells}, {c[1] for c in cells}
    return (
        len(xs) == 1
        and sorted(ys) == list(range(min(ys), min(ys) + len(cells)))
        or len(ys) == 1
        and sorted(xs) == list(range(min(xs), min(xs) + len(cells)))
    )


def check(
    results: dict[int, tuple[int, int, list]],
    free: list[int],
    composite: dict[int, int],
    bar=is_bar,
) -> int:
    k = 0
    for n in range(1, NMAX + 1):
        f, t, tiles = results[n]
        assert f == free[n - 1], f"free count n={n}: {f} != {free[n - 1]}"
        assert len(tiles) == t
        k += 2
        if n in PRIMES or n == 1:
            assert t == 1 and bar(tiles[0]), (
                f"prime n={n}: {t} tilings, first {tiles[:1]}"
            )
            k += 1
        else:
            assert t == composite[n], f"composite n={n}: {t} != {composite[n]}"
            assert t > 1 and any(not bar(c) for c in tiles), (
                f"composite n={n} has only bars"
            )
            k += 2
    assert not bar([(0, 0), (1, 0), (0, 1)]) and bar([(0, 0), (0, 1), (0, 2)]) and bar([(3, 1), (4, 1)])
    return k + 1


def main() -> None:
    with tempfile.TemporaryDirectory() as tmp:
        binary = Path(tmp) / "tilesq"
        subprocess.run(
            ["cc", "-O2", "-o", str(binary), str(HERE / "tilesq.c")], check=True
        )
        results = {n: run(binary, n) for n in range(1, NMAX + 1)}
        print(
            f"positive: {check(results, A000105, COMPOSITE)} assertions passed",
            flush=True,
        )

        trans = {n: run(binary, n, mutant=True) for n in TRANSLATION_ONLY}
        for n, want in TRANSLATION_ONLY.items():
            assert trans[n][1] == want, f"translations-only n={n}: {trans[n][1]}"
            assert trans[n][1] < results[n][1]
        print(
            "control: translations-only build changes every composite count checked",
            flush=True,
        )

        free_bad = A000105.copy()
        free_bad[10] += 1
        mutants = {
            "free count off by one at n=11": (results, free_bad, COMPOSITE, is_bar),
            "composite 12 claimed 54": (
                results,
                A000105,
                {**COMPOSITE, 12: 54},
                is_bar,
            ),
            "translations-only run in place of the full one": (
                {**results, **{n: trans[n] for n in TRANSLATION_ONLY}},
                A000105,
                COMPOSITE,
                is_bar,
            ),
            "bar test accepts every shape": (
                results,
                A000105,
                COMPOSITE,
                lambda c: True,
            ),
            "bar test accepts only vertical bars": (
                results,
                A000105,
                COMPOSITE,
                lambda c: len({x for x, _ in c}) == 1,
            ),
        }
        for name, args in mutants.items():
            try:
                check(*args)
            except AssertionError as e:
                print(f"rejected mutant: {name} ({e})", flush=True)
            else:
                sys.exit(f"UNDETECTED MUTANT: {name}")
        print(f"all {len(mutants)} mutants rejected")


if __name__ == "__main__":
    main()
