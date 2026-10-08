# Ancillary files for "Two Triangulations That Share Only Their Hull"

## 1. Exact checks of the paper's examples and small claims (no external data)

    python3 check_paper.py

Python 3.9 or newer, standard library only, integer arithmetic. It runs in under a second and prints a JSON
summary; any failed check stops it with a nonzero exit code. It is independent of the search code below. It checks:

- the nine-point example of Section 3 (general position, pentagonal hull, both edge sets are triangulations
  sharing only the hull);
- the insertion example of Section 4: `(24,24)` lies in faces 156 and 479 and on no line through two points;
- the worked example of Section 5: side 56 meets the faces 357, 347, 479, 469 of B in that order, so
  (156; 479, 347) is a chain, and after inserting (24,24) the chain is (56p; 347, 47p);
- the configuration in the Lemma 2 figure;
- the formula for the minimum number of shared edges in Section 6, against brute force over all pairs of
  triangulations, on all 246 subsets of 5 to 7 points of the nine-point set and on a convex pentagon;
- the certificates `certificates/n09.json` to `n17.json`: for each n from 9 to 17, two triangulations of n
  points in general position whose only common edges are the five hull edges;
- the seven nine-point witnesses in `witnesses09.txt`: pentagonal hull, oct = 3 so the minimum is exactly 5, no
  nontrivial combinatorial automorphism, and the Section 3 set has the order type of exactly one of them.

- Section 7: Lemma 9 (the convex seed) on the points (i, i^2) for every h from 6 to 30, the two pentagon fans, and
  the seven-point example with a hexagonal hull (triangulations sharing only the six hull edges, the good pair
  137, 245, and the point (6/5, 2/5) inside both);
- chains: the convex seed has the chain (v1v3v5; v2v4v6, v2v6v7) for every h from 7 to 30 and no chain at all for
  h = 6, and the seven-point example has the chain (137; 245, 267).

`witnesses10.txt` lists the 734 ten-point order types attaining five (from the enumeration below).

The checker itself was mutation-tested: injecting a shared interior edge, adding one to the formula, reordering
the faces along side 56, expecting a nontrivial automorphism, and expecting oct = 2 each make it fail. For
Section 7, a shared edge in the seven-point example, a witness point outside the faces, a seed whose second fan
starts at v5, and a wrong face each make it fail.

## 2. The enumeration of Section 6 (needs the order-type database)

The point sets come from the order-type database of Aichholzer, Aurenhammer and Krasser (Order 19 (2002)
265-281), distributed by its authors at http://www.ist.tugraz.at/aichholzer/research/rp/triangulations/ordertypes/
for non-commercial use. It is not redistributed here. Files used: `otypes04.b08` to `otypes08.b08`,
`otypes09.b16`, `otypes10.b16`.

    cc -O2 -o fmin enumeration/fmin.c
    ./fmin otypes09.b16 9 7 -1 0      # about 6 s
    ./fmin otypes10.b16 10 5 -1 0     # about 2 min

`fmin file n F` computes, for every order type, the minimum number of shared edges f(P) when it is at most F,
using f(P) = 6n - 6 - 2h - C(n,2) + oct(P) and an exact odd-cycle-transversal search on the crossing graph. It
prints counts by hull size h. Expected summaries (single core, 2026):

    n=9 sets=158817 F=7  counts by hull size h, f (f=8 means > 7):
      h=3: f7:3 f8:55232
      h=4: f6:53 f7:1291 f8:69131
      h=5: f5:7 f6:306 f7:3211 f8:24708
      h=6: f6:118 f7:1033 f8:3401
      h=7: f7:83 f8:228
      h=8: f8:11
      h=9: f8:1

    n=10 sets=14309547 F=5  counts by hull size h, f (f=6 means > 5):
      h=3: f6:4876476
      h=4: f6:6319019
      h=5: f5:734 f6:2628004
      h=6: f6:450176
      h=7: f6:33969
      h=8: f6:1146
      h=9: f6:22
      h=10: f6:1

The rows give min f = 4, 5, 6, 6, 6, 5, 5 for n = 4..10 (runs for n = 4..8 take well under a second). At n = 9,
exactly 7 order types reach 5 and all have h = 5. At n = 10 it is 734, all with h = 5. The triangular-hull value
at n = 9 is 7 (row h=3 above).

For n = 10 with a triangular hull, `enumeration/oct2.c` gives the value 7. Running `./oct2 otypes10.b16 10 4`
(about 2 min, recorded on 2026-09-28, not rerun for this archive) prints the histogram
`4:1084 5:14308463`. So oct >= 4 for every ten-point set, giving f(P) >= 7 when h = 3, and 7 is attained
(order type 12277679 has h = 3 and oct = 4).

    python3 enumeration/automorph.py witnesses09.txt

lists the combinatorial automorphisms of each witness (all trivial). `check_paper.py` repeats this check
independently.

## Formal check

Theorems 1 and 2 and the lemmas they use are formalised in Lean 4 with Mathlib (standard axioms only). Theorem 2
takes the enumeration result for a pentagonal hull with six to eight points as an explicit hypothesis. The
formalisation is in `../lean/`; see its README for the pinned toolchain,
Mathlib revision, build commands, theorem signatures and the enumeration hypothesis.

## Reproducing the small pentagonal obstruction

`INPUT-HASHES.json` records bytes and SHA-256 hashes for the database inputs.
The database is not redistributed. Its completeness is the external input.

    ./fmin otypes06.b08 6 6 -1 0
    ./fmin otypes07.b08 7 6 -1 0
    ./fmin otypes08.b08 8 6 -1 0

The pentagonal-hull rows are respectively:

    h=5: f6:2 f7:1
    h=5: f6:2 f7:20
    h=5: f6:12 f7:558

Here f7 means strictly greater than 6. In particular, no set in these rows
has minimum shared-edge count 5. The complete rerun output is in `small-search.txt`.
`checker-output.json` records a fresh run of the exact checker.

The search branches on every vertex of an odd cycle, because a deletion set
making the graph bipartite must hit that cycle. Vertex-disjoint odd cycles
give a valid deletion lower bound; integer orientation tests construct the
crossing graph. This certifies exhaustive decision at each supplied budget,
conditional on the completeness of the order-type database.
