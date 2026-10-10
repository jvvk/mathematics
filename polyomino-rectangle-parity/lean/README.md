# Lean formalisation: polyomino rectangles by parity

Lean 4.34.0 with Mathlib v4.34.0. Build with `lake exe cache get && lake build LeanProofs`, then
`lake env lean CheckClaims.lean` prints each result's axioms (only `propext`, `Classical.choice`,
`Quot.sound`, or fewer). `python3 scripts/mutants.py` checks that 8 wrong variants fail.

Cells are `ℤ × ℤ`; `chi` is the checkerboard colour `±1` and `imb S` the sum of `chi` over a finite set. A piece is
placed by one of the eight grid symmetries `lin k` followed by a translation (`place k t`). `Tiles R P k t` says the
placed pieces are pairwise disjoint and their union is `R`; `rect a b` is `[0, a) × [0, b)`.

| Paper | Lean (namespace `NominoParity`) |
|---|---|
| Lemma 1: a placed copy has imbalance `± c(P)` | `chi_add`, `chi_lin`, `chi_place`, `lin_injective`, `place_injective`, `imb_place` |
| Lemma 1: `c(P)` has the parity of the number of squares | `imb_mod_two` |
| Imbalance and area of a tiled region | `imb_tiling`, `card_tiling`, `card_rect` |
| Lemma 2: a rectangle with an even side is balanced | `imb_rect_even` |
| Proposition 1 | `no_rectangle` |
| Theorem 1, given the totals of Table 1 | `no_rectangle_8_10_16` |

## What is not formalised

The totals `S(8) = 278`, `S(10) = 4010` and `S(16) = 13329078` are hypotheses of `no_rectangle_8_10_16`. They come
from enumerating the hole-free n-ominoes, which is a search, done by two independent programs in `verify/`.
