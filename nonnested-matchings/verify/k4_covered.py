"""Theorem 3, Computation 2: covered 16-edge families not handled by Lemma 9(c), its mirror image, or Lemma 9(d).

A covered family is S = (union of the short stars at centres c1 < c2 < c3, cut off at 1 and n) minus omitted edges,
|S| = 16, with no non-nested 4-matching. Range: gaps g1, g2 in 1..16; on each side the centre is at 1..3 (star cut
off) or at 4..11 (0..7 free vertices beyond the star). The enumeration drops families to which Lemma 9(c) applies with
the extra edge (c-2,c) (as computed), its mirror image, or Lemma 9(d), with A, B taken from S. For every remaining
family it finds a window [i, i+3] with c-3 <= i <= c for a centre c that is good: every p < q < r in cyclic order
after i+3 gives a non-nested 4-matching inside S and the star chords (4) of length >= 4. The paper reports 15,984
such families and no failure; Lemma 10 reduces every n to this range.

The work is split into 16 units (first gap g1 = 1..16). Each finished unit is saved in k4_covered_progress.tsv; a
run with --resume skips the units recorded there (a plain run starts afresh); the status line shows progress. Usage:
  python3 k4_covered.py            full run from scratch, about an hour
  python3 k4_covered.py --resume   continue an interrupted full run
  python3 k4_covered.py --list-only   write the leftover identifiers (no window check) for recheck_k4/compare_lists.py
  python3 k4_covered.py --quick    units g1 = 1, 2 only (5,392 families), a few minutes; no progress file
"""

import itertools
import os
import sys

if not __debug__:
    sys.exit("refusing to run under python -O: the checks are assertions")

UNITS = [1, 2] if "--quick" in sys.argv else list(range(1, 17))
PROG = "k4_covered_progress.tsv"


def nested(e, f):
    return (e[0] < f[0] and f[1] < e[1]) or (f[0] < e[0] and e[1] < f[1])


def has_nnk(es, k, M=()):
    if k == 0:
        return True
    for j, e in enumerate(es):
        if any(set(e) & set(f) or nested(e, f) for f in M):
            continue
        if has_nnk(es[j + 1 :], k - 1, M + (e,)):
            return True
    return False


def handled(S, n):
    Ss = set(S)
    for c in range(4, n - 2):
        if {(c - 3, c), (c - 2, c), (c, c + 2)} <= Ss and has_nnk(
            sorted(x for x in S if x[0] >= c + 4), 2
        ):
            return True
        if (
            c + 3 <= n
            and {(c, c + 3), (c, c + 2), (c - 2, c)} <= Ss
            and has_nnk(sorted(x for x in S if x[1] <= c - 4), 2)
        ):
            return True
        if (
            c + 3 <= n
            and {(c - 3, c), (c, c + 3)} <= Ss
            and any(x[1] <= c - 4 for x in S)
            and any(x[0] >= c + 4 for x in S)
        ):
            return True
    return False


def good(Ss, n, i):
    out = [((i + 3 + k - 1) % n) + 1 for k in range(1, n - 3)]
    for p, q, r in itertools.combinations(out, 3):
        st = {
            tuple(sorted(e))
            for e in [
                (i + 1, p),
                (i + 2, q),
                (i + 3, r),
                (p, i),
                (q, i + 1),
                (r, i + 2),
            ]
        }
        st = [e for e in st if e in Ss or e[1] - e[0] >= 4]
        if not has_nnk(sorted(set(st) | Ss), 4):
            return False
    return True


def unit(g1):
    left = 0
    for g2 in range(1, 17):
        for lm in range(11):
            for rm in range(11):
                C = [lm + 1, lm + 1 + g1, lm + 1 + g1 + g2]
                n = C[2] + rm
                full = sorted(
                    {
                        tuple(sorted((c, c + d)))
                        for c in C
                        for d in (-3, -2, -1, 1, 2, 3)
                        if 1 <= c + d <= n
                    }
                )
                for om in (
                    itertools.combinations(full, len(full) - 16)
                    if len(full) >= 16
                    else []
                ):
                    S = [e for e in full if e not in om]
                    if has_nnk(S, 4) or handled(S, n):
                        continue
                    if LIST is not None:
                        idx = [full.index(e) for e in om] + [-1, -1]
                        LIST.append((g1, g2, lm, rm, idx[0], idx[1]))
                        left += 1
                        continue
                    Ss = set(S)
                    windows = sorted(
                        {
                            c + o
                            for c in C
                            for o in (-3, -2, -1, 0)
                            if 1 <= c + o <= n - 3
                        }
                    )
                    assert any(good(Ss, n, i) for i in windows), (
                        "no good near-centre window",
                        g1,
                        g2,
                        lm,
                        rm,
                        om,
                    )
                    left += 1
    return left


if "--list-only" in sys.argv:
    # Write the leftover families as (g1, g2, lm, rm, index of each omitted edge in the sorted list of the centres'
    # short edges, -1 if none): the identifiers printed by recheck_k4/recheck_covered.c. No good-window check.
    LIST = []
    for g1 in range(1, 17):
        unit(g1)
    with open("k4_covered_list.tsv", "w") as f:
        for row in sorted(LIST):
            f.write("\t".join(map(str, row)) + "\n")
    print(f"wrote {len(LIST)} leftover identifiers to k4_covered_list.tsv")
    sys.exit(0)
LIST = None

done = {}
QUICK = "--quick" in sys.argv  # quick runs (also used by the mutation suite) never read or write the progress file
if not QUICK and "--resume" not in sys.argv and os.path.exists(PROG):
    os.remove(PROG)  # a fresh run starts from scratch; only --resume reuses finished units
if not QUICK and "--resume" in sys.argv and os.path.exists(PROG):  # cached progress is trusted only on --resume
    for line in open(PROG):
        g, k = line.split()
        done[int(g)] = int(k)
for g1 in UNITS:
    if g1 in done:
        continue
    done[g1] = unit(g1)
    if not QUICK:
        with open(PROG, "a") as f:
            f.write(f"{g1}\t{done[g1]}\n")
    print(
        f"unit g1={g1}: {done[g1]} families, each with a good near-centre window "
        f"[{len([g for g in UNITS if g in done])}/{len(UNITS)} units, {sum(done[g] for g in UNITS if g in done)} so far]",
        flush=True,
    )
total = sum(done[g] for g in UNITS)
print(
    f"families not handled by the lemmas: {total}; every one has a good window within distance 3 of a centre"
)
if UNITS == list(range(1, 17)):
    assert total == 15984, total
print("ALL CHECKS PASSED")
