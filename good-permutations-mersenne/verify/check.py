"""Good permutations (MO 514690): reproduce every computational claim of the note.

    python3 check.py            # compiles the two C programs with cc, runs them, prints PASS
    MUTANT=1 python3 check.py   # half_search built with a planted error; must print FAIL

1. Theorem 2 (numerically, n = 2^m - 1 <= 2047): the bad blocks of the asker's permutation are
   exactly the prefixes whose length is a proper divisor of n.
2. plain_count (no reduction): every odd n <= 41 other than 3, 7, 31 has no good permutation; the
   counts for 3, 7, 31 are 2, 4, 4, and the good ones are the construction and its symmetries.
3. half_search (the Lean reduction): counts 4, 0, 4, 0 for n = 7, 15, 31, 63, agreeing with
   plain_count on 7, 15, 31. It runs first and the script stops at the first mismatch.
"""
from __future__ import annotations

import os
import subprocess
import sys
import tempfile
from pathlib import Path

HERE = Path(__file__).resolve().parent


def construction(n: int) -> list[int]:
    """The asker's permutation: a_1 = 1, a_t = n + 2 - t - (-1)^t for t >= 2."""
    return [1] + [n + 2 - t - (-1) ** t for t in range(2, n + 1)]


def bad_blocks(a: list[int]) -> set[tuple[int, int]]:
    """(start, length) of proper blocks, length >= 2, with integer average; start is 1-based."""
    n, pre = len(a), [0]
    for x in a:
        pre.append(pre[-1] + x)
    return {(s + 1, L) for L in range(2, n) for s in range(n - L + 1) if (pre[s + L] - pre[s]) % L == 0}


def symmetries(a: list[int]) -> set[tuple[int, ...]]:
    n = len(a)
    comp = [n + 1 - x for x in a]
    return {tuple(a), tuple(a[::-1]), tuple(comp), tuple(comp[::-1])}


def run(exe: Path, n: int) -> tuple[int, list[list[int]], int]:
    out = subprocess.run([str(exe), str(n)], capture_output=True, text=True, timeout=3600,
                         check=True).stdout.split("\n")
    perms = [list(map(int, ln.split())) for ln in out if ln and ln[0].isdigit()]
    summary = next(ln for ln in out if ln.startswith("n="))
    count = int(summary.split("good=")[1].split()[0])
    nodes = int(summary.split("nodes=")[1]) if "nodes=" in summary else 0
    return count, perms, nodes


def main() -> int:
    ok = True
    for m in range(2, 12):
        n = 2**m - 1
        a = construction(n)
        assert sorted(a) == list(range(1, n + 1))
        want = {(1, L) for L in range(2, n) if n % L == 0}
        ok &= bad_blocks(a) == want
    print(f"Theorem 2, n = 3..2047: {'ok' if ok else 'MISMATCH'}")

    with tempfile.TemporaryDirectory() as tmp:
        plain, half = Path(tmp) / "plain", Path(tmp) / "half"
        flags = ["-DMUTANT"] if os.environ.get("MUTANT") else []
        subprocess.run(["cc", "-O2", "-o", str(plain), str(HERE / "plain_count.c")], check=True)
        subprocess.run(["cc", "-O2", *flags, "-o", str(half), str(HERE / "half_search.c")], check=True)

        half_counts: dict[int, int] = {}
        # (n, good permutations, search nodes): the counts in Table 1 of the note
        for n, want, want_nodes in [(7, 4, 23), (15, 0, 855), (31, 4, 85387), (63, 0, 106605579)]:
            c, perms, nodes = run(half, n)
            good = c == want and nodes == want_nodes
            if c:
                good &= {tuple(p) for p in perms} == symmetries(construction(n))
            print(f"half search n = {n}: {c} good permutation(s), {nodes} nodes "
                  f"{'ok' if good else 'MISMATCH'}",
                  flush=True)
            if not good:
                print("FAIL")
                return 1
            half_counts[n] = c

        plain_counts = {}
        for n in range(3, 42, 2):
            c, perms, _ = run(plain, n)
            plain_counts[n] = c
            want = {3: 2, 7: 4, 31: 4}.get(n, 0)
            good = c == want and (c == 0 or {tuple(p) for p in perms} == symmetries(construction(n)))
            ok &= good and half_counts.get(n, c) == c
        print("plain counts, odd n <= 41 (agree with half search on 7, 15, 31):",
              {n: c for n, c in plain_counts.items() if c})

    print("PASS" if ok else "FAIL")
    return 0 if ok else 1


if __name__ == "__main__":
    sys.exit(main())
