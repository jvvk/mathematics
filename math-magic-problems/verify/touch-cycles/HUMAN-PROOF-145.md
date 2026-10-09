# A proof by hand for the (1,4,5) case of Friedman 24

**Theorem.** No nonempty finite arrangement of A, B, and C kings satisfies:
each A touches exactly one B, each B touches exactly four Cs, and each C
touches exactly five As. Touching includes all eight king directions.

This proof uses only neighbour counting. No search result or software
certificate is required.

Choose the highest occupied row and call it row 0. Let its rightmost occupied
cell be (0,0). All cells above row 0, and all cells (x,0) with x>0, are empty.

**Observation 1.** A C on row 0 cannot touch a B. It has at most five available
neighbour positions: two on its own row and three below. Since it needs five
As, none of those positions can contain B. Consequently there is no B on
row 0: such a B would have at most three C neighbours, all below it.

The cell (0,0) is not C either, since it has only four available neighbour
positions. Therefore it is A. Its unique B neighbour lies immediately below
it, in one of the three cells (-1,-1), (0,-1), (1,-1).

**Observation 2 (the counting lemma).** Suppose a B at (u,v) has no C neighbours
in the row above it. Its four C neighbours must then be at

\[
(u-1,v),\quad (u+1,v),\quad (u-1,v-1),\quad (u+1,v-1).
\]

Indeed, there are only five possible C positions in the same row or below,
including the cell (u,v-1) directly beneath B. If that middle cell were C,
it would touch B and the three other C neighbours of B. Four of its eight
neighbours would then be non-A, leaving room for at most four As instead of
five. Thus the middle cell is not C, and the remaining four positions must
all be C.

By Observation 1, this lemma applies to any B on row -1. We now consider the
three possible positions of the unique B touching A at (0,0).

## Case 1: B at (1,-1)

The counting lemma forces C at (2,-1). Its three neighbours (1,0), (2,0),
and (3,0) are empty, and it also touches B at (1,-1). This leaves at most
four A neighbours. Contradiction.

## Case 2: B at (0,-1)

The lemma forces Cs at (1,-1) and (1,-2). The C at (1,-1) touches that B,
the C at (1,-2), and the two empty cells (1,0), (2,0). Again four neighbour
positions are unavailable for As. Contradiction.

## Case 3: B at (-1,-1)

The lemma forces Cs at (-2,-1), (0,-1), (-2,-2), and (0,-2).
Consider C at (0,-1). Its neighbours already include B at (-1,-1), C at
(0,-2), and the empty cell (1,0). It needs five As, so every other neighbour
must be A. In particular, these five cells are A:

\[
(-1,-2),\quad (1,-2),\quad (1,-1),\quad (-1,0),\quad (0,0).
\]

The A at (1,-1) must touch a B. Its only possible B neighbours are (2,-1)
and (2,-2): all six other neighbours are already A, C, or empty.

But (2,-1) cannot be B. Its three neighbours on row 0 are empty, and its
neighbours (1,-1), (1,-2) are A. Only three positions remain for Cs, whereas
a B needs four. Therefore (2,-2) must be B.

The forced part of the arrangement is now:

```text
             x = -2 -1  0  1  2  3
row  0            ?  A  A  .  .  .
row -1            C  B  C  A  ?  ?
row -2            C  A  C  A  B  ?
```

Here dots denote empty cells; question marks are unrestricted.

This new B at (2,-2) has no C neighbours in the row above it. The left one,
(1,-1), is A. Neither (2,-1) nor (3,-1) can be C: each touches three empty
cells on row 0 and this new B, leaving at most four places for As.

Applying the counting lemma to B at (2,-2) now forces C at (1,-2). But that
cell was already forced to be A. Contradiction.

All three cases are impossible. Therefore the proposed finite arrangement
does not exist. **QED.**

This resolves one of the four triples in problem 24 by a geometric proof.
The complete four-triple result is presently documented in `PROOF.md` using
computer-assisted certificates; this note does not replace those other
three proofs.
