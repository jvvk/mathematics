"""Enumerate mosaic floorplans (generic rectangular dissections of a square, no + junctions)
by inserting a new room at the top-left corner (Nakano 2001), deduplicating by canonical form.
A room is (x1, x2, y1, y2) in segment-index coordinates: x = 0 .. V+1, y = 0 .. H+1, every
internal index is its own maximal segment. Counts must equal the Baxter numbers."""

from __future__ import annotations

Room = tuple[int, int, int, int]
BAXTER = [1, 2, 6, 22, 92, 422, 2074, 10754, 58202, 326240, 1882960]


def canon(rooms: list[Room]) -> tuple[Room, ...]:
    xs = sorted({c for r in rooms for c in r[:2]})
    ys = sorted({c for r in rooms for c in r[2:]})
    xm = {x: i for i, x in enumerate(xs)}
    ym = {y: i for i, y in enumerate(ys)}
    return tuple(sorted((xm[a], xm[b], ym[c], ym[d]) for a, b, c, d in rooms))


def children(fp: tuple[Room, ...]) -> list[tuple[Room, ...]]:
    rooms = list(fp)
    top = max(r[3] for r in rooms)
    out = []
    # rooms touching the left boundary, from the top down
    left = sorted([r for r in rooms if r[0] == 0], key=lambda r: -r[3])
    for k in range(1, len(left) + 1):
        bottom = left[k - 1][2]
        new = []
        for r in rooms:
            if r[0] == 0 and r[2] >= bottom:
                new.append((0.5, r[1], r[2], r[3]))  # pushed right by the new column
            else:
                new.append(r)
        new.append((0, 0.5, bottom, top))
        out.append(canon(new))
    # rooms touching the top boundary, from the left to the right
    topr = sorted([r for r in rooms if r[3] == top], key=lambda r: r[0])
    for k in range(1, len(topr) + 1):
        right = topr[k - 1][1]
        new = []
        for r in rooms:
            if r[3] == top and r[1] <= right:
                new.append((r[0], r[1], r[2], top - 0.5))  # pushed down by the new row
            else:
                new.append(r)
        new.append((0, right, top - 0.5, top))
        out.append(canon(new))
    return out


def all_floorplans(n: int) -> list[set]:
    levels = [{((0, 1, 0, 1),)}]
    for _ in range(n - 1):
        nxt = set()
        for fp in levels[-1]:
            nxt.update(children(fp))
        levels.append(nxt)
    return levels


if __name__ == "__main__":
    import sys

    N = int(sys.argv[1])
    for i, lev in enumerate(all_floorplans(N), 1):
        print(i, len(lev), "Baxter", BAXTER[i - 1], "OK" if len(lev) == BAXTER[i - 1] else "MISMATCH")
