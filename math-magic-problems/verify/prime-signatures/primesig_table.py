"""Check Friedman's February 2018 prime-signature table (data/primesig_table.json).

Signature of n: its prime exponents sorted in decreasing order, as a tuple; the table writes (2, 1) as "21".
Checks:
  1. every published value n has signature A and n+1 has signature B (sympy factorint);
  2. every published value up to LIMIT is the smallest such n, and every "none" or "?" cell has no
     n up to LIMIT (one pass over a smallest-prime-factor sieve).
Usage: python3 primesig_table.py [LIMIT]   (default 3*10^6, about 40 s single core)
"""

from __future__ import annotations

import json
import sys
from array import array
from pathlib import Path

from sympy import factorint

DATA = Path(__file__).resolve().parent / "data" / "primesig_table.json"


def sig_of_factors(exps: list[int]) -> tuple[int, ...]:
    return tuple(sorted(exps, reverse=True))


def parse(s: str) -> tuple[int, ...]:
    """Friedman's notation: one digit per exponent ("21" = p^2 q)."""
    return tuple(int(ch) for ch in s)


def sig(n: int) -> tuple[int, ...]:
    return sig_of_factors(list(factorint(n).values()))


def spf_sieve(limit: int) -> array:
    spf = array("I", range(limit + 1))
    i = 2
    while i * i <= limit:
        if spf[i] == i:
            for j in range(i * i, limit + 1, i):
                if spf[j] == j:
                    spf[j] = i
        i += 1
    return spf


def sig_spf(n: int, spf: array) -> tuple[int, ...]:
    exps: list[int] = []
    while n > 1:
        p, e = spf[n], 0
        while n % p == 0:
            n //= p
            e += 1
        exps.append(e)
    return sig_of_factors(exps)


def main(limit: int) -> None:
    cells = json.load(open(DATA))
    wrong = 0
    for c in cells:
        if c["n"] is not None:
            n = c["n"]
            if (sig(n), sig(n + 1)) != (parse(c["A"]), parse(c["B"])):
                wrong += 1
                print("WRONG SIGNATURE", c, sig(n), sig(n + 1), factorint(n + 1))
    published = sum(c["n"] is not None for c in cells)
    print(f"signatures: {published - wrong} of {published} published values correct")

    wanted = {(parse(c["A"]), parse(c["B"])) for c in cells}
    first: dict[tuple[tuple[int, ...], tuple[int, ...]], int] = {}
    spf = spf_sieve(limit + 1)
    prev = sig_spf(2, spf)
    for n in range(2, limit + 1):
        nxt = sig_spf(n + 1, spf)
        key = (prev, nxt)
        if key in wanted and key not in first:
            first[key] = n
        prev = nxt
    bad = 0
    for c in cells:
        f = first.get((parse(c["A"]), parse(c["B"])))
        if c["n"] is not None and c["n"] <= limit and f != c["n"]:
            bad += 1
            print("NOT SMALLEST", c, f)
        if c["n"] is None and f is not None:
            bad += 1
            print("FOUND FOR", c["status"], c, f)
        if c["n"] is not None and c["n"] > limit and f is not None:
            bad += 1
            print("SMALLER THAN PUBLISHED", c, f)
    small = sum(c["n"] is not None and c["n"] <= limit for c in cells)
    print(
        f"minimality to {limit}: {small} values confirmed smallest, {bad} disagreements"
    )


if __name__ == "__main__":
    main(int(sys.argv[1]) if len(sys.argv) > 1 else 3_000_000)
