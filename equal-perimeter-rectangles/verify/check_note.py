"""Checks every explicit claim the note makes about the five n = 9 dissections, directly from their
integer coordinates (no linear algebra, no enumeration): each is a dissection of the square
(pieces inside it, pairwise disjoint interiors, areas summing to side^2), all perimeters are equal,
no two pieces are congruent, and the coordinates are in lowest terms. Also checks the
three-piece worked example of Section 2."""
from __future__ import annotations

import json
import sys
from fractions import Fraction as F
from math import gcd

fails = 0


def check(cond: bool, msg: str) -> None:
    global fails
    print(("PASS " if cond else "FAIL ") + msg)
    fails += not cond


def dissection_ok(side, rects) -> bool:
    inside = all(0 <= a < b <= side and 0 <= c < d <= side for a, b, c, d in rects)
    area = sum((b - a) * (d - c) for a, b, c, d in rects) == side * side
    disjoint = all(
        min(p[1], q[1]) <= max(p[0], q[0]) or min(p[3], q[3]) <= max(p[2], q[2])
        for i, p in enumerate(rects) for q in rects[i + 1:]
    )
    return inside and area and disjoint


sols = json.load(open("noncongruent_9.json"))
check(len(sols) == 5, "five solutions recorded")
check([s["side"] for s in sols] == [72, 84, 86, 161, 165], "sides 72, 84, 86, 161, 165")
check([s["perimeter"] for s in sols] == [130, 130, 130, 260, 260], "perimeters 130, 130, 130, 260, 260")
for s in sols:
    side, R = s["side"], [tuple(r) for r in s["rects"]]
    tag = f"side {side}:"
    check(len(R) == 9, f"{tag} nine pieces")
    check(dissection_ok(side, R), f"{tag} pieces tile the square")
    per = {2 * ((b - a) + (d - c)) for a, b, c, d in R}
    check(per == {s["perimeter"]}, f"{tag} every perimeter is {s['perimeter']}")
    shapes = {tuple(sorted((b - a, d - c))) for a, b, c, d in R}
    check(len(shapes) == 9, f"{tag} no two pieces congruent")
    areas = {(b - a) * (d - c) for a, b, c, d in R}
    check(len(areas) == 9, f"{tag} all areas different (equivalent, given equal perimeters)")
    g = 0
    for r in R:
        for c in r:
            g = gcd(g, c)
    check(gcd(g, side) == 1, f"{tag} coordinates in lowest terms")

# The 84 x 84 example printed in the introduction, as [x1,x2] x [y1,y2]
intro = [(0, 15, 34, 84), (0, 31, 0, 34), (15, 36, 40, 84), (15, 74, 34, 40), (36, 74, 40, 67),
         (36, 84, 67, 84), (31, 74, 12, 34), (31, 84, 0, 12), (74, 84, 12, 67)]
check(dissection_ok(84, intro) and {(b - a) + (d - c) for a, b, c, d in intro} == {65}
      and len({tuple(sorted((b - a, d - c))) for a, b, c, d in intro}) == 9, "introduction example valid")


def key(R, side):
    imgs = []
    for k in range(8):
        img = []
        for a, b, c, d in R:
            x1, x2, y1, y2 = (c, d, a, b) if k & 4 else (a, b, c, d)
            if k & 1:
                x1, x2 = side - x2, side - x1
            if k & 2:
                y1, y2 = side - y2, side - y1
            img.append((x1, x2, y1, y2))
        imgs.append(tuple(sorted(img)))
    return min(imgs)


check(key(intro, 84) == key([tuple(r) for r in sols[1]["rects"]], 84), "introduction example is the side-84 solution")

# Section 2 example: one vertical cut at x, right part cut at height y; side 1, semi-perimeter s.
x, y = F(1, 4), F(1, 2)
s = x + 1
check((1 - x) + y == s and (1 - x) + (1 - y) == s, "three-piece example: x=1/4, y=1/2, s=5/4 solves the system")
sys.exit(1 if fails else 0)
