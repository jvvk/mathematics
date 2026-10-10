# Polyomino rectangles by parity: no rectangle for 8, 10 or 16 cells

<!-- visual:start -->
<p align="center"><img src="https://raw.githubusercontent.com/jvvk/jvvk/129b8257bb0779ecb5a1e65fb9f7835201249e50/assets/polyomino-parity.svg" width="760" alt="Polyomino rectangles by parity"></p>

<p align="center"><b>One copy of every hole-free n-omino tiles no rectangle for n = 8, 10 or 16, because the pieces' checkerboard imbalances add up to 2 mod 4 (for n = 16, over 11,230,003 pieces). Sizes 9 and 11 to 15 stay open.</b><br><sub>Partial progress · parity argument formally verified in Lean · totals by two independent enumerations</sub></p>

<p align="center"><sub><a href="paper">paper</a> · <a href="lean">Lean proof</a> · <a href="verify">code</a> · <a href="../">all results</a></sub></p>
<!-- visual:end -->

Can one copy of every hole-free `n`-omino tile a rectangle? On [MathOverflow 378923](https://mathoverflow.net/q/378923) (Ralph Morrison, 2020) the answer is yes for `n = 1, 2, 5, 7`, no for `n = 3, 4, 6` by a parity argument, and no for `n ≥ 17` by cavity arguments in the answers (Stanley, Budd, Lehner; `n = 17` by Hoffman's computer count). The cases `8 ≤ n ≤ 16` were open.

**Theorem.** For `n = 8`, `10` and `16` the answer is no.

The reason is the checkerboard count that rules out 4 and 6. A placed piece covers `±c(P)` more black than white squares; for even `n` every `c(P)` is even and the rectangle is balanced, so `∑ c(P)` must be a multiple of 4. Over all hole-free `n`-ominoes the total `S(n)` is

| n | 8 | 10 | 12 | 14 | 16 |
|---|---|---|---|---|---|
| pieces | 363 | 4,460 | 58,937 | 805,475 | 11,230,003 |
| S(n) | 278 | 4,010 | 59,248 | 886,436 | 13,329,078 |
| S(n) mod 4 | **2** | **2** | 0 | 0 | **2** |

For `n = 12`, `14` and every odd `n` the count gives no obstruction, so `9, 11, 12, 13, 14, 15` remain open.

Preprint v1, 10 October 2026, not peer reviewed and not yet independently reviewed. The parity argument is formally verified in Lean 4 (`lean/`, standard axioms only) for any pieces and any placements; the three totals are its hypotheses, computed by two independent enumerations that both reproduce OEIS A000104, A000105 and A001168 for `n ≤ 16`. The author used AI tools (Claude, Anthropic) in this work, as described in the paper's acknowledgement, and is responsible for its content.

## Contents

- `paper/`: `note.tex`, `note.pdf`, the figure `fig_pieces.tex` and its generator `make_fig.py`.
- `lean/`: a Lake project pinned to Lean 4.34.0 and Mathlib v4.34.0; `lean/README.md` maps results to Lean names, `CheckClaims.lean` prints their axioms, `scripts/mutants.py` runs 8 mutation tests.
- `verify/`:
  - `parity.c`: Redelmeier enumeration of fixed `n`-ominoes with a hole test, checkerboard imbalance and stabiliser size; Burnside weights give the free counts and `S(n)`.
  - `check.py`: builds `parity.c`, checks the counts against OEIS, recomputes `n ≤ 10` in pure Python, checks the table, the figure's octominoes and the sign choices where the count is silent; each claim has a mutant (three broken C builds and a Python one).
  - `recheck/grow.c`, `recheck/recheck.py`: an independent enumeration (free pieces grown level by level in a hash table) that recomputes every count and `S(n)`; a stripe-colouring mutant is caught.

## Reproduce

```
cd verify && python3 check.py --full            # about 3 minutes; without --full stops at n = 14
cd recheck && python3 recheck.py --full         # about 5 minutes, 630 MB at n = 16
cd ../../paper && latexmk -pdf note.tex
cd ../lean && lake exe cache get && lake build LeanProofs && lake env lean CheckClaims.lean
```

## Licence

The paper is released under [CC BY 4.0](../LICENSE-PAPERS), the code under the [MIT licence](../LICENSE-CODE).
