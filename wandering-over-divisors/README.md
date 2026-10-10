# Wandering over the divisors of a power of ten

<!-- visual:start -->
<p align="center"><img src="https://raw.githubusercontent.com/jvvk/jvvk/f4b02f4c7053c3f0eb40fb0b3cf32b587bdc429b/assets/divisor-walk.svg" width="760" alt="Losing squares on the 9 × 9 board"></p>

<p align="center"><b>Players multiply by 2 or 5 or divide by 10, never repeating a divisor of 10ⁿ. The tournament's natural answer fails from 10⁶ on, and the second player beats whole families of openings on every board.</b><br><sub>Partial progress · theorems formally verified in Lean 4</sub></p>

<p align="center"><sub><a href="paper">paper</a> · <a href="lean">Lean proof</a> · <a href="verify">code</a> · <a href="../">all results</a></sub></p>
<!-- visual:end -->

A referee names a divisor of `10^n`; two players then take turns multiplying the last number named by 2 or by 5, or dividing it by 10, always naming a new divisor of `10^n`; the player who cannot move loses. Writing `2^x 5^y` as the square `(x, y)`, this is a piece on the board `{0, …, n}²` with steps `(1,0)`, `(0,1)` and `(−1,−1)`. The game is problem 20 of the 23rd All-Ukrainian Tournament of Young Mathematicians (2020), posted by Witold on Mathematics Stack Exchange (question 3689425) and by Vepir on MathOverflow (question 363120), where it has had no answer since 2020.

The note proves:

- **Theorem 1.** For `n = 2, 4, 6, 8` the second player wins from 4, 9, 20 and 31 squares. So from a random divisor of `10^6` the first player wins with probability **29/49**, and the natural answer `1 − (k+1)²/(2k+1)²` to the tournament's part (b) is false from `n = 6` on.
- **Lemma 2.** Sweeping an edge: once the piece reaches the right-hand edge with the column below it unused, the second player wins.
- **Theorem 3.** From a diagonal square `(k, k)`, `k < n`, the openings `(1,0)` and `(0,1)` lose; so `(−1,−1)` is the only possible winning opening.
- **Theorem 5.** From a bottom-row square `(a, 0)`, `1 ≤ a ≤ n`, `n ≥ 2`, the opening `(0,1)` loses; so `(1,0)` is the only possible winning opening.
- **Theorem 7.** The corners `(n, 0)`, `(0, n)` and the square `(2, 0)` lose for the first player when `n ≥ 2`, and `(2, 2)` when `n ≥ 3`.

It also records Vepir's conjectured pattern for odd `n` (Conjecture 8, checked on every square up to `10 × 10`, with `3m² − 4m + 5` losing squares on the `2m × 2m` board), and approaches that fail: copying, square weightings (no weighting decides the winner on `5 × 5` or `7 × 7`), and induction over rectangles.

Preprint, 10 October 2026, not peer reviewed. Lemma 2 and Theorems 3, 5 and 7 are formally verified in Lean 4 for every board size (`lean/`, standard axioms only). The exposition has not yet been independently reviewed. The author used an AI tool (Claude, Anthropic) in this work, as described in the note's acknowledgements, and is responsible for its content.

## Contents

- `paper/`: `note.tex`, `note.pdf`, `gen_figs.py` (draws the figures from `verify/data`) and the generated figures.
- `verify/`:
  - `solve.c`: exact solver (negamax, table keyed on the position and the unused squares still reachable). `data/sqN.txt` are its tables for the `N × N` boards, `N ≤ 10`; `data/rect/` holds the `R × C` tables quoted in Section 8.
  - `verify_note.py`: an independent solver in Python, sharing no code with `solve.c`, that recomputes every board up to `9 × 9`, compares them square by square with the C tables, and checks Theorem 1, Theorems 3, 5 and 7, Conjecture 8 and its count formula, and the copying example of Section 8; seven planted wrong statements are rejected.
  - `brute.py`: plain brute force with no table, used to test `solve.c` on small boards; `claims.c`: the theorem statements checked with `solve.c` up to `9 × 9`.
  - `extra/`: the square-weighting test of Section 8 (`weights.c` samples positions; `weight_test.py` and `weight_test_rel.py` solve the parity and threshold systems exactly).
- `lean/`: a Lake project pinned to Lean 4.34.0 and Mathlib v4.34.0. `lean/README.md` maps the results to Lean names; `SOURCE-SNAPSHOT.json` records the development commit and file hashes; `scripts/mutants.py` plants ten wrong changes, each rejected.

## Reproduce

```
cd verify
cc -O2 -o solve solve.c && ./solve 7 7          # the 7 x 7 table, rows from the top
python3 verify_note.py 8                         # independent check up to 9 x 9; about a minute
cd ../paper && python3 gen_figs.py && latexmk -pdf note.tex
cd ../lean && lake exe cache get && lake build LeanProofs
lake env lean CheckClaims.lean                   # axiom audit
python3 scripts/mutants.py                       # ten mutants, each rejected
```

## Licence

The paper is released under [CC BY 4.0](../LICENSE-PAPERS), the code under the [MIT licence](../LICENSE-CODE).
