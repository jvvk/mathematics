# The easiest dice to tell apart

<!-- visual:start -->
<p align="center"><img src="https://raw.githubusercontent.com/jvvk/jvvk/b12cf1aa0a34407c585c34ebb39821571a23cb4b/assets/easiest-dice.svg" width="760" alt="The easiest dice to tell apart"></p>

<p align="center"><b>Among loaded dice whose faces are capped at probability r, a staircase against its own reversal is the easiest pair to tell apart, for any number of faces and rolls; this answers an open Math.SE question with its equality cases.</b><br><sub>Open problem settled · formally verified in Lean · equality cases for two rolls partly open</sub></p>

<p align="center"><sub><a href="paper">paper</a> · <a href="lean">Lean proof</a> · <a href="verify">code</a> · <a href="../">all results</a></sub></p>
<!-- visual:end -->

Two dice have `k` faces, and no face of either die comes up with probability more than `r`. Roll one of them `n` times; the overlap `∑_w min(P(w), Q(w))` is twice the error of the best guess at which die it was. [Math.SE 5149864](https://math.stackexchange.com/q/5149864) (September 2026) asked for the least overlap when `k = 4` and `1/3 < r < 1/2`, conjectured the value given by the pair `(r, s, r, 0)`, `(0, r, s, r)` with `s = 1 − 2r`, and asked for all equality cases.

**Theorem 1.** For every `k`, every cap `r ≥ 1/k` and every `n`, the least overlap is attained by the staircase `p* = (r, …, r, 1 − mr, 0, …, 0)`, `m = ⌊1/r⌋`, against its reversal; the dice may even change from roll to roll. For `k = 4` and `1/3 < r < 1/2` this is the asker's pair, so the asker's value is exact (for example `6/25` at `n = 2`, `r = 2/5`).

**Theorem 2** (`k = 4`). Equality holds for `n = 1` exactly when `max(pᵢ, qᵢ) = r` on every face, and for `n ≥ 3` only for the asker's pair with its faces relabelled. For `n = 2` the family `p = (r, r, x, s − x)`, `q = (0, s, r, r)` also attains it; whether there are others is not settled here.

The one-roll step is three lines: any `a` faces carry at most `min(1, ar)` of a capped die and at least `max(0, 1 − (k − a)r)`, and the first `a` faces of the staircase pair meet both limits at once, so it wins at every exchange rate. Carrying that through `n` rolls is the standard product step (Blackwell 1953; Kairouz, Oh and Viswanath 2015). The equality cases come from three exchange rates that the proof passes through.

Preprint v1, 10 October 2026, not peer reviewed and not yet independently reviewed. Every theorem and lemma is formally verified in Lean 4 (`lean/`, standard axioms only); the asker's closed form and the equality cases are also checked in exact arithmetic. The author used AI tools (Claude, Anthropic) in this work, as described in the paper's acknowledgement, and is responsible for its content.

## Contents

- `paper/`: `note.tex`, `note.pdf` and the figures `fig_stair.tex`, `fig_rolls.tex`.
- `lean/`: a Lake project pinned to Lean 4.34.0 and Mathlib v4.34.0; `lean/README.md` maps results to Lean names, `CheckClaims.lean` prints their axioms, `scripts/mutants.py` and `scripts/mutants_equality.py` run 10 and 9 mutation tests.
- `verify/`:
  - `check.py`: exact rational checks of the one-roll domination for `k ≤ 7` at every breakpoint, the many-roll inequality for random mixed dice, the asker's closed form for `n ≤ 6`, and the equality cases for `n ≤ 4`; each claim has a mutant that must fail.
  - `recheck/recheck.py`: an independent numerical search for a capped pair with smaller overlap (shares no code with `check.py`); none is found, the search reaches the staircase value, and a relaxed cap is caught.

## Reproduce

```
cd verify && python3 check.py
cd recheck && python3 recheck.py            # needs numpy; about a minute
cd ../../paper && latexmk -pdf note.tex
cd ../lean && lake exe cache get && lake build LeanProofs && lake env lean CheckClaims.lean
```

## Licence

The paper is released under [CC BY 4.0](../LICENSE-PAPERS), the code under the [MIT licence](../LICENSE-CODE).
