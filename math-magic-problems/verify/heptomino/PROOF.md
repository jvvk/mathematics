# Friedman unsolved problem 15, shape A: impossible in every square (2026-09-28)

Shape A is the leftmost heptomino in the list's picture (0507/unsolved.gif, read 2026-09-28):

    .##
    .#.
    .#.
    .#.
    ##.

**Theorem.** No arrangement of one or more non-overlapping copies of A (rotations and reflections allowed)
in an n x n square has the same positive number of occupied cells in every row and every column.

**Proof.** Row counts of A are P = (2,1,1,1,2), column counts Q = (1,5,1); both are palindromes, so every
orientation has profiles P and Q, possibly exchanged. Weight cell (x,y) by w[x] + w[y]. A copy then weighs
P.w[i..i+4] + Q.w[j..j+2]. If every P-window is >= -1 and every Q-window is >= 1, every copy weighs >= 0,
so any union of copies does. A balanced arrangement with c cells per line weighs 2c sum(w). So it is
enough to give, for each n >= 5, weights with sum(w) < 0 and those window bounds.

- n = 5..9: explicit exact weights (exact-weights-A.jsonl, found by Codex, rechecked here).
- n = 5K + m, K >= 1, m = 5..9: w = [a_K Z + d, ..., a_1 Z + d, C_m] with Z = (-5,1,0,-1,5),
  d = (-1/2,1/2,0,1/2,-1/2), a_1 = 7/2, a_{k+1} = 5 a_k, and the cores C_m in shapeA_family.json.
  Each block sums to 0, so sum(w) = sum(C_m) < 0. Windows inside a block are independent of its scale
  (Z contributes 0) and meet the bounds through d. A window across a boundary between scales 5s and s
  equals A s + D with A > 0, and holds at s = a_1, so it holds at every deeper boundary. Windows at the
  core are fixed and checked. The leftmost block has fewer windows. Sides below 5 cannot hold A.

Check (standard library only): `/usr/bin/python3 -S -B check_shapeA.py 400` verifies sides 5..400
explicitly, the induction step symbolically, and rejects four mutants (bad core, ratio 4, no offset,
wrong profile). Shapes B, C and D stay open: their fractional placement relaxations are feasible on some
larger sides (Codex), so no weighting of this kind can exclude them there.

Credit: exact finite certificates for sides 5..50 by Codex (friedman15); the all-n family and proof here.
