#!/usr/bin/env python3
"""Literal ternary-state check, exhaustive local checks, no author code used."""

import csv
from itertools import product


def literal_orbit(seed):
    k = len(seed)
    x = [None] + list(seed)
    seen = {tuple(seed): 0}
    while True:
        n = len(x)
        x.append((x[-1] + x[n - k] ** 2) % 3)
        state = tuple(x[-k:])
        j = len(x) - 1 - k  # state window starts at j+1
        if state in seen:
            return x, seen[state], j - seen[state]
        seen[state] = j


rows = list(
    csv.DictReader(
        open("independent_results.txt").read().split("PASS:")[0].splitlines()
    )
)
# Coverage: the table must hold exactly one row for each k = 2..60, or nothing below has been checked.
assert [int(row["k"]) for row in rows] == list(range(2, 61)), (
    "independent_results.txt must list k = 2..60 once each"
)
captures = []
for row in rows:
    k = int(row["k"])
    x, mu, period = literal_orbit([0] * (k - 1) + [1])
    assert (mu, period) == (int(row["mu"]), int(row["period"]))
    if period == 4:
        captures.append(k)
        # Extend long enough to include the second qualifying endpoint.
        for _ in range(8 * k + 20):
            n = len(x)
            x.append((x[-1] + x[n - k] ** 2) % 3)
        G = (k + 2) // 4
        endpoints = []
        for s in range(k + 1, len(x) - 4 * G):
            if all((x[n] == 0) == ((n - s) % 4 == 0) for n in range(s, s + 4 * G + 1)):
                endpoints.append(s + 4 * G)
        z = endpoints[0]
        assert (z, z - 4 * G) == (int(row["z"]), int(row["s"]))
        if k == 2:
            print(
                "k=2: x[1:17] =",
                x[1:17],
                "; mu=",
                mu,
                "; s=",
                z - 4 * G,
                "; z=",
                z,
                sep="",
            )
            relaxed = next(
                s + 4 for s in range(1, len(x) - 4) if x[s : s + 5] == [0, 1, 1, 2, 0]
            )
            print("k=2 with r>=1 instead of r>=k+1: z=", relaxed, sep="")
        if k == 3:
            print(
                "k=3: x[1:16] =",
                x[1:16],
                "; mu=",
                mu,
                "; s=",
                z - 4 * G,
                "; z=",
                z,
                sep="",
            )
        if k == 6:
            print(
                "k=6: first two qualifying endpoints =",
                endpoints[:2],
                "; z-mu =",
                [z0 - mu for z0 in endpoints[:2]],
            )
print("Literal full-state orbit check: PASS for every k=2..60")
print("Capturing k:", captures)

# Exhaust the actual integer-offset lists, independent of any trajectory.
for k in range(6, 61):
    if k % 4 not in (2, 3):
        continue
    G = (k + 2) // 4
    blocks = range(0, 4 * G, 4)  # m-s
    images = [[m + j - k for m in blocks] for j in (4, 1, 2)]
    ends = (2, -1, 0) if k % 4 == 2 else (1, -2, -1)
    assert images == [list(range(j - k, e + 1, 4)) for j, e in zip((4, 1, 2), ends)]
    if k % 4 == 2:
        assert -2 in images[0] and -1 in images[1] and -4 in images[2]
    else:
        assert -3 in images[0] and -2 in images[1]
        assert -5 in images[2] and -1 in images[2]
    if k in (6, 7):
        print(f"k={k}: offsets for (m+4-k,m+1-k,m+2-k) = {images}")
print("Step 1 list endpoints/membership: PASS for all eligible k=6..60")
print("Step 2 parenthetical k=4t+3: (s+1-k)-s mod 4 =", (1 - 7) % 4, "; claimed 1")

admissible = []
for middle in product((1, 2), repeat=3):
    block = (0,) + middle + (0,)
    if all((block[i + 1] - block[i]) % 3 in (0, 1) for i in range(4)):
        admissible.append(block)
assert admissible == [(0, 1, 1, 2, 0), (0, 1, 2, 2, 0)]
print("Lemma 17 exhaustive nonzero-interior blocks:", admissible)

# Prop. 12: all 3^4 candidate periodic words at every requested k.
for k in range(2, 61):
    valid = {
        w
        for w in product(range(3), repeat=4)
        if all(w[i] == (w[(i - 1) % 4] + w[(i - k) % 4] ** 2) % 3 for i in range(4))
    }
    expected = {(0, 0, 0, 0)}
    if k % 4 in (2, 3):
        base = (0, 1, 1, 2) if k % 4 == 2 else (0, 1, 2, 2)
        expected |= {base[i:] + base[:i] for i in range(4)}
    assert valid == expected
print("Prop. 12 exhaustive: PASS, 81 words for each k=2..60")

# Prop. 13 local sufficiency and Lemma 17, from EVERY ternary seed
# through k=9. No standard initial-data assumption in these assertions.
seeds = runs = blocks_checked = 0
for k in range(2, 10):
    G = (k + 2) // 4
    for seed in product(range(3), repeat=k):
        seeds += 1
        x = [None] + list(seed)
        end = 3 * k + 4 * G + 16
        for n in range(k + 1, end + 1):
            x.append((x[n - 1] + x[n - k] ** 2) % 3)
        for r in range(k + 1, end - 3):
            block = x[r : r + 5]
            if block[0] == block[4] == 0 and all(block[j] for j in (1, 2, 3)):
                blocks_checked += 1
                assert tuple(block) in admissible
        if k % 4 not in (2, 3):
            continue
        for r in range(k + 1, end - 4 * G + 1):
            z = r + 4 * G
            if not all((x[n] == 0) == ((n - r) % 4 == 0) for n in range(r, z + 1)):
                continue
            runs += 1
            cycle = (0, 1, 1, 2) if k % 4 == 2 else (0, 1, 2, 2)
            # Exact sufficient state equality establishes the entire future,
            # rather than just comparing a finite suffix.
            assert x[z] == cycle[0]
            assert all(
                (x[n] != 0) == (cycle[(n - z) % 4] != 0)
                for n in range(z - k + 1, z + 1)
            )
            assert all(x[n] == cycle[(n - z) % 4] for n in range(z, end + 1))
print(
    f"All ternary seeds k=2..9: PASS; seeds={seeds}, lemma blocks={blocks_checked}, capture runs={runs}"
)
