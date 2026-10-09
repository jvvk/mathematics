"""Independent check of cert_dD.txt for squarefree N = 2d (d = 3, 5).

For squarefree N every abelian group of order N is cyclic, so a sublattice L of
index N in Z^m is the kernel of v -> a.v mod N for some a in (Z_N)^m with the
map onto. A polycube P tiles by translations of L iff its N cells hit N
distinct residues. So P lattice-tiles iff some a in (Z_N)^m separates its cells.
This shares no code with unfold.c (no Hermite normal forms).

Each stated lattice certificate is also checked directly: |det| = N and no
difference of two cells lies in the lattice (exact rational solve).
"""

from __future__ import annotations

import itertools
import re
import sys
from fractions import Fraction

import numpy as np


def parse(path: str) -> list[tuple[np.ndarray, list[list[int]] | None]]:
    out = []
    for line in open(path):
        cells = [
            tuple(map(int, c.split(","))) for c in re.findall(r"\(([-\d,]+)\)", line)
        ]
        lat = line.split("lattice=")[1].strip()
        rows = (
            None
            if lat == "none"
            else [
                list(map(int, r.split(","))) for r in re.findall(r"\[([-\d,]+)\]", lat)
            ]
        )
        out.append((np.array(cells, dtype=np.int64), rows))
    return out


def det(rows: list[list[int]]) -> Fraction:
    a = [[Fraction(x) for x in r] for r in rows]
    n, d = len(a), Fraction(1)
    for c in range(n):
        p = next((r for r in range(c, n) if a[r][c] != 0), None)
        if p is None:
            return Fraction(0)
        if p != c:
            a[c], a[p] = a[p], a[c]
            d = -d
        d *= a[c][c]
        for r in range(c + 1, n):
            f = a[r][c] / a[c][c]
            a[r] = [x - f * y for x, y in zip(a[r], a[c])]
    return d


def in_lattice(v: tuple[int, ...], rows: list[list[int]]) -> bool:
    """Solve x B = v exactly; v is in the lattice iff x is integral."""
    n = len(rows)
    a = [[Fraction(rows[r][c]) for r in range(n)] + [Fraction(v[c])] for c in range(n)]
    for c in range(n):
        p = next(r for r in range(c, n) if a[r][c] != 0)
        a[c], a[p] = a[p], a[c]
        for r in range(n):
            if r != c and a[r][c] != 0:
                f = a[r][c] / a[c][c]
                a[r] = [x - f * y for x, y in zip(a[r], a[c])]
    return all((a[i][n] / a[i][i]).denominator == 1 for i in range(n))


def main(path: str, N: int) -> None:
    reps = parse(path)
    m = reps[0][0].shape[1]
    A = np.array(
        list(itertools.product(range(N), repeat=m)), dtype=np.int64
    ).T  # m x N^m
    agree = tilers = bad_cert = 0
    for cells, rows in reps:
        assert cells.shape == (N, m)
        res = np.sort((cells @ A) % N, axis=0)
        separated = bool(np.any(np.all(np.diff(res, axis=0) != 0, axis=0)))
        tilers += separated
        agree += separated == (rows is not None)
        if rows is not None:
            ok = abs(det(rows)) == N and not any(
                in_lattice(tuple(int(x) for x in cells[i] - cells[j]), rows)
                for i in range(N)
                for j in range(i + 1, N)
            )
            bad_cert += not ok
    print(
        f"{path}: unfoldings={len(reps)} lattice_tilers={tilers} agree_with_unfold={agree} bad_certificates={bad_cert}"
    )


if __name__ == "__main__":
    main(sys.argv[1], int(sys.argv[2]))
