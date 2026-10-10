# Binary words with the same characteristic polynomial: a block-reversal lemma and a census to length 22

<!-- visual:start -->
<p align="center"><img src="https://raw.githubusercontent.com/jvvk/jvvk/bb1500db34d630be2664feaa17db3a4f2acc35cf/assets/binary-words.svg" width="760" alt="Binary words with the same characteristic polynomial"></p>

<p align="center"><b>When do two binary words give tridiagonal matrices with the same characteristic polynomial? One block-reversal lemma, with complementation, explains 805 of the 822 coincidences up to length 22; 17 sporadic ones are left open.</b><br><sub>Partial progress · lemma and families formally verified in Lean · census by computation</sub></p>

<p align="center"><sub><a href="paper">paper</a> · <a href="lean">Lean proof</a> · <a href="verify">code</a> · <a href="../">all results</a></sub></p>
<!-- visual:end -->

Each binary word gives a tridiagonal matrix, with the word on the diagonal and ones beside it. On [MathOverflow 514920](https://mathoverflow.net/q/514920) Philip Weiss (2026) asked when two words that are not reverses of each other give the same characteristic polynomial, and how many distinct polynomials there are.

**Lemma.** Write `M_w` for the transfer matrix of a word, so that `P_{AVB} = x_Aᵀ M_V y_B`. If a symmetric `2 × 2` matrix `G` makes every `M_{Yᵢ} G` symmetric, and `G x_A = λ y_{B'}`, `G x_{A'} = λ y_B` with `λ ≠ 0`, then

`P(A Y₁ ⋯ Yₘ B) = P(A' Yₘ ⋯ Y₁ B')`.

Reversal, the interleaving family from the earlier answer and a new ratio-class family (Theorem R) are three cases. Up to length 22 the lemma, with complementation `P_{w̄}(t) = (−1)ⁿ P_w(1 − t)`, explains 805 of the 822 classes of words that share a polynomial:

| n | 8 | 9 | 12 | 13 | 16 | 18 | 19 | 20 | 22 |
|---|---|---|---|---|---|---|---|---|---|
| distinct polynomials a_n | 134 | 270 | 2,072 | 4,154 | 32,856 | 131,249 | 262,604 | 524,606 | 2,097,843 |
| coincidence classes | 2 | 2 | 8 | 6 | 40 | 78 | 52 | 194 | 333 |
| unexplained | 0 | 2 | 0 | 2 | 0 | 1 | 4 | 2 | 4 |

The values of `a_n` for `16 ≤ n ≤ 22` are new; the full table is in the paper. The first unexplained class is `111010100 ~ 100110110`.

Preprint v1, 10 October 2026, not peer reviewed and not yet independently reviewed. The lemma, both families, the complement identity and the facts used to cancel `λ` are formally verified in Lean 4 (`lean/`, standard axioms only); the census is a computation, with every move it uses confirmed exactly over ℚ(t) and an independent recheck. The author used AI tools (Claude, Anthropic) in this work, as described in the paper's acknowledgement, and is responsible for its content.

## Contents

- `paper/`: `note.tex`, `note.pdf`, the figure `fig_blocks.tex` and its generator `make_fig.py`.
- `lean/`: a Lake project pinned to Lean 4.34.0 and Mathlib v4.34.0; `lean/README.md` maps results to Lean names, `CheckClaims.lean` prints their axioms, `scripts/mutants.py` runs 11 mutation tests.
- `verify/`:
  - `enum.c`: all words of length `n ≤ 22` up to reversal, fingerprinted at two points modulo 2⁶¹ − 1; `exact.py` confirms every class with integer polynomials.
  - `classify.py`: the census; the conditions on `G` are linear and are solved modulo a large prime at random points.
  - `exactcheck.py`: every move the census uses, confirmed with sympy over ℚ(t); `gtypes.py` sorts the moves into interleavings, Theorem R and other.
  - `soundtest.py`: exhaustively for `n ≤ 8`, the search never accepts a move between words with different polynomials.
  - `check.py`: runs all of the above against the numbers in the paper; each claim has a mutant that is caught.
  - `recheck/recheck.py`: an independent program (own recurrence, own move search, exact rational arithmetic) that recounts `a_n` for `n ≤ 18` and redoes the census for `n ≤ 16`.

## Reproduce

```
cd verify && python3 check.py                   # about 8 minutes; needs sympy and a C compiler
cd recheck && python3 recheck.py                # about 15 seconds
cd ../../paper && latexmk -pdf note.tex
cd ../lean && lake exe cache get && lake build LeanProofs && lake env lean CheckClaims.lean
```

## Licence

The paper is released under [CC BY 4.0](../LICENSE-PAPERS), the code under the [MIT licence](../LICENSE-CODE).
