# Five from inverse pairs

<!-- visual:start -->
<p align="center"><img src="https://raw.githubusercontent.com/jvvk/jvvk/d7d7e84935d54f1859ff5f0ffb7494f5b2bf4168/assets/inverse-pairs.svg" width="760" alt="Five from inverse pairs"></p>

<p align="center"><b>Summing 1/√(a·ā) over a and its inverse mod p gives 5 + O(p^(−1/8+ε)): the inverse pairs behave like all pairs, and those sum to (∑ 1/√a)²/p → 4.</b><br><sub>Answers a question · in Lean, assuming Weil's bound</sub></p>

<p align="center"><sub><a href="paper">paper</a> · <a href="lean">Lean proof</a> · <a href="verify">code</a> · <a href="../">all results</a></sub></p>
<!-- visual:end -->

For a prime `p` let `S(p) = ∑ 1/√(a·ā)` over `a = 1, …, p−1`, where `ā` is the inverse of `a` modulo `p` in `1, …, p−1`. Nilotpal Kanti Sinha asked on Mathematics Stack Exchange ([question 5146740](https://math.stackexchange.com/q/5146740)) whether `S(p) → 5`, as computations suggested. This note proves `S(p) = 5 + O(p^(−1/8+ε))` (Theorem 1).

The proof compares the inverse pairs `(a, ā)` with all pairs `(a, b)`, scaled by `1/p`. The all-pairs sum factors as `C(p) = (∑ 1/√a)²/p`, which tends to `4` by telescoping square roots (Lemma 2), and the term `a = 1` gives the remaining `1`. An exact layer-cake identity turns `S(p) − 1 − C(p)` into a weighted sum, over heights `m`, of the difference between the two counts under the hyperbola `xy = m`. For large `m` that difference is controlled by Weil's bound for Kloosterman sums, counted in rectangles and stacked into staircases (Lemmas 3 and 4). For small `m` the divisor bound controls it (Lemma 5).

Preprint v1, 10 October 2026, not peer reviewed. Every step except Weil's bound is formally verified in Lean 4 (`lean/`, standard axioms only). Weil's bound (1948) is not in Mathlib; it enters the Lean theorems as an explicit hypothesis, never as an axiom. The author used AI tools (Claude, Anthropic) in this work, as described in the paper's acknowledgement, and is responsible for its content.

## Contents

- `paper/`: `note.tex` and `note.pdf`; `figs/` holds the TikZ figure data written by `verify/figs.py`.
- `verify/`:
  - `sums.c`: `S(p)`, `C(p)` and `S(p) − 1 − C(p)` for primes near given starting points (Table 1), with inverses by the extended Euclidean algorithm.
  - `check.py`: an independent Python check, with inverses by a different recurrence. It compiles `sums.c` and compares the two on `p` up to `10^6`. It also checks Lemma 3 on random and extreme rectangles, Lemma 4 over every height for `p = 101, 211, 401`, the inequality of Lemma 5, the layer-cake identity (2) to `10^−15`, and Lemma 2 for all primes below 3000. `MUTANT=1`, `2` and `3` plant errors (a wrong inverse, the wrong normalisation of `C`, a staircase without its column width); each must print `FAIL`.
  - `figs.py`: Figure 1; asserts the counts in its caption.
- `lean/`: a Lake project pinned to Lean 4.34.0 and Mathlib v4.34.0; `lean/README.md` maps results to Lean names, `CheckClaims.lean` prints their axioms, `scripts/mutants.py` runs the mutation tests.

## Reproduce

```
cd verify && python3 check.py && for m in 1 2 3; do MUTANT=$m python3 check.py | tail -1; done
cc -O2 -o sums sums.c -lm && ./sums 1009 10007 100003 1000003 10000019 100000007
python3 figs.py
cd ../paper && latexmk -pdf note.tex
cd ../lean && lake exe cache get && lake build LeanProofs && lake env lean CheckClaims.lean
```

## Licence

The paper is released under [CC BY 4.0](../LICENSE-PAPERS), the code under the [MIT licence](../LICENSE-CODE).
