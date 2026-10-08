"""Figures for the note (figs/*.tex). Run: python3 figs/make_figs.py

Every figure asserts the properties it illustrates (general position, containment, emptiness of faces,
which faces form a good pair) before writing TikZ. The nine-point example is read from data/n09.json.
"""
from __future__ import annotations

import json
from fractions import Fraction as F
from itertools import combinations
from pathlib import Path

from geom import cr, faces_of, general_position, good_pairs, hull_edges, oriented, overlap, separated

OUT = Path(__file__).parent
BLUE, RED = "layerA", "layerB"


def inside(tri, q) -> bool:
    a, b, c = tri
    s = [cr(a, b, q), cr(b, c, q), cr(c, a, q)]
    return all(v > 0 for v in s) or all(v < 0 for v in s)


def c(q, s=1.0, x0=0.0):
    return f"({float(q[0]) * s + x0:.3f},{float(q[1]) * s:.3f})"


def seg(a, b, style, s=1.0, x0=0.0):
    return f"\\draw[{style}] {c(a, s, x0)} -- {c(b, s, x0)};\n"


def tri(pts, style, s=1.0, x0=0.0):
    return f"\\path[{style}] " + " -- ".join(c(q, s, x0) for q in pts) + " -- cycle;\n"


def dot(q, s=1.0, x0=0.0):
    return f"\\node[vertex] at {c(q, s, x0)} {{}};\n"


def lab(q, text, pos, s=1.0, x0=0.0, style=""):
    return f"\\node[{pos}{',' + style if style else ''}] at {c(q, s, x0)} {{{text}}};\n"


def save(name, body, opts=""):
    (OUT / f"{name}.tex").write_text(f"\\begin{{tikzpicture}}[{opts}]\n{body}\\end{{tikzpicture}}\n")


# ------------------------------------------------------------------ 1. the nine-point example, numbered
d = json.load(open(OUT / "data" / "n09.json"))
P = [tuple(p) for p in d["points"]]
A = {tuple(sorted(e)) for e in d["A"]}
B = {tuple(sorted(e)) for e in d["B"]}
H = hull_edges(P)
assert general_position(P) and len(H) == 5 and A & B == H and len(A) == len(B) == 19
cx, cy = sum(p[0] for p in P) / 9, sum(p[1] for p in P) / 9
POS = {1: "above", 2: "right", 3: "right", 4: "below right", 5: "above right", 6: "below left",
       7: "above left", 8: "below", 9: "left"}
s, gap = 0.125, 8.6
b = ""
for k, (E, col, title) in enumerate(((A, BLUE, "Triangulation $A$"), (B, RED, "Triangulation $B$"))):
    x0 = k * gap
    for e in sorted(E - H):
        b += seg(P[e[0]], P[e[1]], f"draw={col},line width=.7pt", s, x0)
    for e in sorted(H):
        b += seg(P[e[0]], P[e[1]], "hull", s, x0)
    for i, q in enumerate(P, start=1):
        b += dot(q, s, x0) + lab(q, f"${i}$", POS[i] + "=1.5pt", s, x0, "font=\\footnotesize")
    b += f"\\node at ({23.5 * s + x0:.3f},-0.75) {{{title}}};\n"
save("nine", b)
FA, FB = faces_of(A, P), faces_of(B, P)
assert ((0, 4, 5), (3, 6, 8)) in good_pairs(P, FA, FB)          # faces 156 and 479
assert inside([P[0], P[4], P[5]], (24, 24)) and inside([P[3], P[6], P[8]], (24, 24))
assert all(cr(P[i], P[j], (24, 24)) != 0 for i, j in combinations(range(9), 2))

# ------------------------------------------------------------------ 2. insertion, schematic (three panels)
al = [(F(0), F(0)), (F(10), F(3, 5)), (F(21, 5), F(9))]
be = [(F(6, 5), F(31, 5)), (F(48, 5), F(37, 5)), (F(32, 5), F(-9, 5))]
p = (F(5), F(39, 10))
assert general_position(al + be + [p])
assert inside(al, p) and inside(be, p)
assert not any(inside(al, v) for v in be) and not any(inside(be, v) for v in al)
Q = overlap(al + be, (0, 1, 2), (3, 4, 5))
s, gap = 0.34, 4.6
b = ""
titles = ["the faces $\\alpha$ and $\\beta$ overlap", "in $A'$: join $p$ to $\\alpha$", "in $B'$: join $p$ to $\\beta$"]
for k in range(3):
    x0 = k * gap
    if k in (0, 1):
        b += tri(al, f"fill={BLUE}!{14 if k == 0 else 8}", s, x0) + tri(al, f"draw={BLUE},line width=.8pt", s, x0)
    if k in (0, 2):
        b += tri(be, f"fill={RED}!{14 if k == 0 else 8}", s, x0) + tri(be, f"draw={RED},line width=.8pt", s, x0)
    if k == 0:
        b += tri(Q, "fill=gray!30", s, x0)
    if k == 1:
        b += "".join(seg(p, v, f"draw={BLUE},line width=1.8pt", s, x0) for v in al)
    if k == 2:
        b += "".join(seg(p, v, f"draw={RED},line width=1.8pt", s, x0) for v in be)
    b += "".join(dot(v, s, x0) for v in (al if k != 2 else []) + (be if k != 1 else []))
    b += dot(p, s, x0) + lab(p, "$p$", "below right=1pt", s, x0)
    if k in (0, 1):
        b += lab(al[2], "$\\alpha$", "left=4pt", s, x0, f"text={BLUE}")
    if k in (0, 2):
        b += lab(be[1], "$\\beta$", "right=3pt", s, x0, f"text={RED}")
    b += f"\\node at ({5 * s + x0:.3f},-1.2) {{\\small {titles[k]}}};\n"
save("insert", b)

# ------------------------------------------------------------------ 3. the chain of faces along xy
fr = lambda a, b_: (F(a), F(b_))
x, y, z, pp = fr(0, 0), fr(7, 0), fr("2.8", "2.05"), fr("3.9", "0.75")
qa, qb, qc, qd, qe = fr("1.6", "1.35"), fr("1.75", "-1.1"), fr("4.25", "1.45"), fr("4.35", "-1.2"), fr("5.55", "1.3")
T = {"T1": (x, qa, qb), "T2": (qb, qa, qc), "beta": (qb, qc, qd), "Tk": (qd, qc, qe), "Tm": (qd, qe, y)}
alpha = (x, y, z)
assert general_position([x, y, z, pp, qa, qb, qc, qd, qe])
assert inside(T["beta"], pp) and inside(alpha, pp)
assert not any(inside(alpha, v) for v in (qa, qb, qc, qd, qe))
assert not any(inside(t, z) for t in T.values())
for i, j in combinations(T, 2):
    assert separated([*T[i], *T[j]], (0, 1, 2), (3, 4, 5)), (i, j)
first = lambda t: min(xx for xx in (F(k, 100) for k in range(1, 700)) if inside(t, (xx, F(0))))
assert sorted(T, key=lambda n: first(T[n])) == ["T1", "T2", "beta", "Tk", "Tm"]
assert not separated([x, pp, y, *T["Tk"]], (0, 1, 2), (3, 4, 5))       # pxy overlaps T_k
L = {"T1": fr(".95", "-.45"), "T2": fr("2.5", "1.0"), "beta": fr("3.7", "-.5"), "Tk": fr("4.9", ".8"), "Tm": fr("6.1", "-.25")}
assert all(inside(T[n], L[n]) for n in T)
s = 1.1
b = tri(alpha, f"fill={BLUE}!10", s) + tri((x, pp, y), "fill=gray!25", s) + tri(T["Tk"], f"fill={RED}!15", s)
for t in T.values():
    b += tri(t, f"draw={RED},line width=.7pt", s)
b += seg(x, z, f"draw={BLUE},line width=.8pt", s) + seg(z, y, f"draw={BLUE},line width=.8pt", s)
for v in (x, y, z):
    b += seg(pp, v, f"draw={BLUE},line width=1.3pt", s)
b += seg(x, y, f"draw={BLUE},line width=1.3pt", s)
b += "".join(dot(v, s) for v in (x, y, z, pp, qa, qb, qc, qd, qe))
b += lab(x, "$x$", "below left", s) + lab(y, "$y$", "below right", s) + lab(z, "$z$", "above", s)
b += lab(fr("3.52", "1.0"), "$p$", "inner sep=1pt", s) + lab(fr("2.75", "1.55"), "$\\alpha$", "inner sep=1pt", s, style=f"text={BLUE}")
for n, text in (("beta", "$\\beta$"), ("Tk", "$\\gamma$")):
    b += lab(L[n], text, "fill=white,inner sep=1pt", s)
save("chain", b)

# ------------------------------------------------------------------ 4. Lemma 3 (sweep), a triangular hull
U, V, W = (0, 0), (12, 0), (0, 12)
Q, R, T = (2, 3), (5, 3), (3, 6)
SP = [U, V, W, Q, R, T]
assert general_position(SP) and len(hull_edges(SP)) == 3
dist = {q: q[0] + q[1] for q in SP if q != U}            # distance to m: x + y = 0, up to the factor 1/sqrt 2
assert min(dist, key=dist.get) == Q and sorted(dist.values())[1] > dist[Q]
assert not any(0 < q[0] + q[1] < dist[Q] for q in SP)     # the open strip between m and l is empty
s = 0.42
b = ""
b += f"\\path[fill=black!10] {c((0, 0), s)} -- {c((5, 0), s)} -- {c((0, 5), s)} -- cycle;\n"
b += f"\\draw[dashed] {c((-2.2, 2.2), s)} -- {c((2.2, -2.2), s)} node[right] {{$m$}};\n"
b += f"\\draw[dashed] {c((-1.0, 6.0), s)} -- {c((6.0, -1.0), s)} node[right] {{$\\ell$}};\n"
for e in ((U, V), (V, W), (W, U)):
    b += seg(e[0], e[1], "hull", s)
b += seg(U, Q, f"draw={BLUE},line width=1.6pt", s)
for q, nm, ps in ((U, "$u$", "below left"), (V, "$v$", "below"), (W, "$w$", "left"), (Q, "$q$", "above right"),
                  (R, "", ""), (T, "", "")):
    b += dot(q, s) + (lab(q, nm, ps, s) if nm else "")
b += f"\\node at {c((8.2, 1.6), s)} {{$H$}};\n"
save("sweep", b)
# ------------------------------------------------------------------ 7. the convex seed, h = 8
OCT = [(100, 0), (71, 71), (0, 100), (-71, 71), (-100, 0), (-71, -71), (0, -100), (71, -71)]
h8 = len(OCT)
assert general_position(OCT) and len(hull_edges(OCT)) == h8
HO = hull_edges(OCT)
# labels v_1..v_h are indices 0..h-1; A: triangle v1 v3 v5 + fan from v5; B: triangle v2 v4 v6 + fan from v2
AO = HO | {(0, 2), (2, 4), (0, 4)} | {(4, k) for k in range(6, h8)}
BO = HO | {(1, 3), (3, 5), (1, 5)} | {(1, k) for k in range(6, h8)}
AO = {tuple(sorted(e)) for e in AO}
BO = {tuple(sorted(e)) for e in BO}
assert AO & BO == HO and len(AO) == len(BO) == 2 * h8 - 3
FAO, FBO = faces_of(AO, OCT), faces_of(BO, OCT)
assert len(FAO) == len(FBO) == h8 - 2
assert ((0, 2, 4), (1, 3, 5)) in good_pairs(OCT, FAO, FBO)
s, gap = 0.0165, 4.4
b = ""
posO = ["right", "above right", "above", "above left", "left", "below left", "below", "below right"]
for k, (E, col, tri_, title) in enumerate(((AO, BLUE, (0, 2, 4), "Triangulation $A$"),
                                          (BO, RED, (1, 3, 5), "Triangulation $B$"))):
    x0 = k * gap
    b += tri([OCT[i] for i in tri_], f"fill={col}!12", s, x0)
    for e in sorted(E - HO):
        b += seg(OCT[e[0]], OCT[e[1]], f"draw={col},line width=.8pt", s, x0)
    for e in sorted(HO):
        b += seg(OCT[e[0]], OCT[e[1]], "hull", s, x0)
    b += "".join(dot(q, s, x0) + lab(q, f"$v_{i + 1}$", posO[i], s, x0, "font=\\footnotesize")
                 for i, q in enumerate(OCT))
    b += f"\\node at ({x0:.3f},-2.5) {{{title}}};\n"
save("convex", b)

# ------------------------------------------------------------------ 8. seven points, hexagonal hull
S7 = [(1, 2), (0, 0), (1, 0), (4, 1), (5, 2), (6, 6), (2, 1)]
lab7 = lambda spec: {tuple(sorted((int(t[0]) - 1, int(t[1]) - 1))) for t in spec.split()}
H7 = hull_edges(S7)
A7 = H7 | lab7("13 14 15 17 37 47")
B7 = H7 | lab7("24 25 26 27 57 67")
assert general_position(S7) and H7 == lab7("12 23 34 45 56 16")
assert A7 & B7 == H7 and len(A7) == len(B7) == 3 * 7 - 3 - 6
FA7, FB7 = faces_of(A7, S7), faces_of(B7, S7)
assert len(FA7) == len(FB7) == 2 * 7 - 6 - 2
assert ((0, 2, 6), (1, 3, 4)) in good_pairs(S7, FA7, FB7)       # faces 137 and 245
w7 = (F(6, 5), F(2, 5))
assert inside([S7[0], S7[2], S7[6]], w7) and inside([S7[1], S7[3], S7[4]], w7)
s, gap = 0.62, 5.2
b = ""
pos7 = ["above left", "below left", "below", "below right", "right", "above", "below"]
for k, (E, col, title) in enumerate(((A7, BLUE, "Triangulation $A$"), (B7, RED, "Triangulation $B$"))):
    x0 = k * gap
    for e in sorted(E - H7):
        b += seg(S7[e[0]], S7[e[1]], f"draw={col},line width=.8pt", s, x0)
    for e in sorted(H7):
        b += seg(S7[e[0]], S7[e[1]], "hull", s, x0)
    b += "".join(dot(q, s, x0) + lab(q, f"${i + 1}$", pos7[i] + "=1pt", s, x0, "font=\\footnotesize")
                 for i, q in enumerate(S7))
    b += f"\\node at ({3 * s + x0:.3f},-0.75) {{{title}}};\n"
save("seven", b)
print("figures written")
