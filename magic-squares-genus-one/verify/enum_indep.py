"""Claude's independent degree-m enumeration and end-to-end filter run (audit of the Theorem C chain).

Enumerates every centre-pair table: points with multiplicities mu_P (a partition of m), columns eps_P in
[-mu_P, mu_P]^4 with at least three entries of absolute value mu_P (Lemma 1), rows summing to 0, and
k_i = sum max(eps_iP, 0) != 1. Technique: per multiplicity class, multisets of columns grouped by their row-sum
vector, then joined across classes on the zero total (meet in the middle for the class of size 6).
Then:
  1. compares the canonical set with mconfigs.configs (independently written recursion);
  2. applies base group law (grouplaw_exact.decide), centre_distinct.reason, and audit_sextic.verdict;
  3. reports survivors (target: none).
"""

from __future__ import annotations

import itertools
import json
import sys
from pathlib import Path
from collections import Counter, defaultdict

from audit_sextic import verdict
from centre_distinct import reason as distinct_reason
from grouplaw_exact import decide


def partitions(n: int, cap: int | None = None):
    cap = n if cap is None else cap
    if n == 0:
        yield ()
        return
    for p in range(min(n, cap), 0, -1):
        for rest in partitions(n - p, p):
            yield (p,) + rest


def cols(mu: int) -> list[tuple[int, ...]]:
    return [
        c
        for c in itertools.product(range(-mu, mu + 1), repeat=4)
        if sum(abs(t) == mu for t in c) >= 3
    ]


def vsum(cs) -> tuple[int, ...]:
    cs = list(cs)
    return tuple(sum(c[i] for c in cs) for i in range(4))


def multisets_by_sum(C: list, n: int, target: tuple[int, ...] | None = None) -> dict:
    """{row-sum vector: [multisets (sorted index tuples) of size n]}; only `target` if given (needed for n >= 5)."""
    out = defaultdict(list)
    if n <= 4 or (n == 5 and target is None):        # n = 5: 2.6M multisets, still fine in full
        for idx in itertools.combinations_with_replacement(range(len(C)), n):
            sm = vsum(C[i] for i in idx)
            if target is None or sm == target:
                out[sm].append(idx)
        return out
    assert target is not None
    h = n // 2
    hi_by_sum = defaultdict(list)
    for idx in itertools.combinations_with_replacement(range(len(C)), n - h):
        hi_by_sum[vsum(C[i] for i in idx)].append(idx)
    for a in itertools.combinations_with_replacement(range(len(C)), h):
        sa = vsum(C[i] for i in a)
        need = tuple(t - x for t, x in zip(target, sa))
        for b in hi_by_sum.get(need, []):
            if b[0] >= a[-1]:                     # each sorted multiset arises exactly once
                out[target].append(a + b)
    return out


def canon(table: list[tuple[int, ...]]) -> tuple:
    """table: columns (mu, e1..e4). Canonical under row sign flips and permutations of points."""
    best = None
    for sg in itertools.product((1, -1), repeat=4):
        key = tuple(
            sorted((c[0],) + tuple(s * t for s, t in zip(sg, c[1:])) for c in table)
        )
        if best is None or key < best:
            best = key
    return best


def enumerate_all(m: int) -> set:
    found = set()
    for part in partitions(m):
        groups = Counter(part)
        per = []
        for mu, n in sorted(groups.items()):
            C = cols(mu)
            single = len(groups) == 1
            per.append((mu, C, multisets_by_sum(C, n, (0, 0, 0, 0) if single else None)))

        # join classes on total zero
        def rec(g, acc_sum, acc_cols):
            if g == len(per):
                if all(v == 0 for v in acc_sum):
                    rows = [[c[1 + i] for c in acc_cols] for i in range(4)]
                    if all(sum(max(t, 0) for t in r) != 1 for r in rows):
                        found.add(canon(acc_cols))
                return
            mu, C, by = per[g]
            if g == len(per) - 1:
                need = tuple(-v for v in acc_sum)
                for idx in by.get(need, []):
                    rec(g + 1, (0, 0, 0, 0), acc_cols + [(mu,) + C[i] for i in idx])
                return
            for sm, lst in by.items():
                for idx in lst:
                    rec(
                        g + 1,
                        tuple(x + y for x, y in zip(acc_sum, sm)),
                        acc_cols + [(mu,) + C[i] for i in idx],
                    )

        rec(0, (0, 0, 0, 0), [])
    return found


def main():
    m = int(sys.argv[1]) if len(sys.argv) > 1 else 6
    mine = enumerate_all(m)
    import mconfigs

    theirs = set()
    for part in mconfigs.partitions(m):
        for cfg in mconfigs.configs(part):
            theirs.add(canon([tuple(c) for c in cfg]))
    print(
        f"m={m}: independent tables {len(mine)}, mconfigs tables {len(theirs)}, equal sets: {mine == theirs}"
    )
    stats, survivors = Counter(), []
    for tab in sorted(mine):
        cfg = [list(c) for c in tab]
        rows = [[c[1 + i] for c in cfg] for i in range(4)]
        A = [r[1:] for r in rows if any(r)]
        base = decide(A, len(cfg))
        if base == "none":
            stats["base group law"] += 1
            continue
        r = distinct_reason(cfg)
        if r != "survives":
            stats[r] += 1
            continue
        v = verdict(cfg)
        stats[v.split(" C=")[0]] += 1
        if v == "SURVIVES":
            survivors.append({"cfg": cfg, "k": [sum(max(x, 0) for x in r) for r in rows], "aug": base})
    print(dict(stats))
    print("survivors:", len(survivors))
    if mine != theirs:
        sys.exit("FAIL: the two enumerations differ")
    if m <= 6 and survivors:
        sys.exit(f"FAIL: {len(survivors)} tables survive in degree {m}")
    if m >= 7:  # input of the degree-seven filters (centre_septic.py and later)
        Path(__file__).with_name(f"m{m}_survivors.json").write_text(json.dumps(survivors))
        print(f"wrote m{m}_survivors.json")


if __name__ == "__main__":
    main()
