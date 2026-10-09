# Deleting the powers of four

<!-- visual:start -->
<p align="center"><img src="https://raw.githubusercontent.com/jvvk/jvvk/cccf1bc1d96309cd055ad0bad24309c65d1a255a/assets/powers-of-four.svg" width="760" alt="Deleting the powers of four"></p>

<p align="center"><b>Delete 16, 64, 256, … from the natural numbers and the number of ways to write n as an ordered sum of three survivors still rises at every step.</b><br><sub>Answers a question · Proposition 1 in Lean</sub></p>

<p align="center"><sub><a href="paper">paper</a> · <a href="lean">Lean proof</a> · <a href="verify">code</a> · <a href="../">all results</a></sub></p>
<!-- visual:end -->

Let `R_{A,h}(n)` count the ordered `h`-tuples from a set `A` of natural numbers that add up to `n`. Sándor and Yang ([arXiv:2606.28849](https://arxiv.org/abs/2606.28849), Remark 1.3) asked whether `R_{A,h}` is strictly increasing for `A = ℕ ∖ {4^(j+2) : j ≥ 0}`. It is, for every `h ≥ 3` and from `n = 0` on (Proposition 1).

Bell and Shallit's Theorem 1 ([arXiv:2212.12473](https://arxiv.org/abs/2212.12473)) already gives strict increase for all large `n`, and the argument is the coefficient computation of their Theorem 2. What the note adds is the explicit bound `R_{A,3}(N) − R_{A,3}(N−1) ≥ N + 1 − 3m(N) − m(N)²` (Lemma 2), valid for every deleted set, with `m(N)` the number of deleted elements up to `N`, and the reduction from every `h ≥ 3` to `h = 3` (Lemma 3). It also records two facts about Sándor and Yang's Problem 1.4, which asks which densities below 1 are possible: no eventually periodic set of density strictly between 0 and 1 works (Proposition 4), and any set that works has `A(N)³ ≥ (N+1)(N+2)/2` (Proposition 5). A density-3/4 candidate passes an exact check up to 262,144 but is unproved (Remark 6).

Preprint v1, 9 October 2026, not peer reviewed. Lemmas 2 and 3 and Proposition 1 are formally verified in Lean 4 (`lean/`, standard axioms only); Propositions 4 and 5 are proved by hand. The author used AI tools (Codex, OpenAI; Claude, Anthropic) in this work, as described in the paper's acknowledgement, and is responsible for its content.

## Contents

- `paper/`: `note.tex`, `note.pdf`, and `make_figs.py`, which computes the figure data and asserts the bound at every plotted point.
- `verify/`:
  - `check_small.py`: `R_{A,3}`, `R_{A,4}`, `R_{A,5}` by direct convolution up to `N = 600`, the bound of Lemma 2 at every `N`, and a direct triple count at sample points. `--mutant` deletes `{4n+2}` instead and must fail.
  - `verify_remark13.py`: the identity behind Lemma 2, from the deleted set alone, through `N = 10^6`, and `h = 3, …, 10` by dense convolution through 512 (writes `remark13-verification.json`).
  - `explore/`: the quadratic-block candidates of Remark 6 (`explore_quadratic_blocks.py` and its outputs). Evidence, not proofs.
- `lean/`: a Lake project pinned to Lean 4.34.0 and Mathlib v4.34.0; `lean/README.md` maps results to Lean names, `CheckClaims.lean` prints their axioms, `scripts/mutants.py` runs the mutation tests.

## Reproduce

```
cd verify
python3 check_small.py 600 && python3 verify_remark13.py
python3 explore/explore_quadratic_blocks.py --q 4 --fill-prefix 25 --limit 262144   # Remark 6, a few minutes
cd ../paper && python3 make_figs.py && latexmk -pdf note.tex
cd ../lean && lake exe cache get && lake build LeanProofs && lake env lean CheckClaims.lean
```

## Licence

The paper is released under [CC BY 4.0](../LICENSE-PAPERS), the code under the [MIT licence](../LICENSE-CODE).
