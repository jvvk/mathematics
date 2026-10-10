# A sequence that looks back half way

<!-- visual:start -->
<p align="center"><img src="https://raw.githubusercontent.com/jvvk/jvvk/18ab19ac1becb7cb94c9ece4ba84df57506b7335/assets/half-window.svg" width="760" alt="A sequence that looks back half way"></p>

<p align="center"><b>If a(n) drops by a(⌊n/2⌋)/n at each odd step, then n a(n) tends to 1/(1 − ln 2), as a commenter guessed from the digits.</b><br><sub>Answers a question · in Lean</sub></p>

<p align="center"><sub><a href="paper">paper</a> · <a href="lean">Lean proof</a> · <a href="verify">code</a> · <a href="../">all results</a></sub></p>
<!-- visual:end -->

Let `a(1) = 1`, `a(n) = a(n−1)` for even `n`, and `a(n) = a(n−1) − a((n−1)/2)/n` for odd `n`. The user AAK asked on Mathematics Stack Exchange ([question 4748129](https://math.stackexchange.com/q/4748129)) for the constant `A` with `n a(n) → A`; Tian Vlasic suggested `A = 1/(1 − ln 2)` from its digits. This note proves it (Theorem 1).

The key is an exact identity (Lemma 2): `n a(n) = 1 + Σ a(k)` over the window `n/2 ≤ k < n`. It makes `n a(n)` equal to `1` plus a weighted average of earlier values, with total weight tending to `ln 2 < 1` (Lemma 3, from Euler's constant). The error `e(n) = n a(n) − A` then satisfies `|e(n)| ≤ s(n) max |e(k)| + A |s(n) − ln 2|` over the window, and since `s(n) ≤ 3/4` eventually, the error shrinks to zero.

Preprint v1, 10 October 2026, not peer reviewed. Every step of the proof is formally verified in Lean 4 (`lean/`, standard axioms only); the rate in Remark 4 is numerical. An answer with this proof was posted to the question (answer 5150836). The author used AI tools (Claude, Anthropic) in this work, as described in the paper's acknowledgement, and is responsible for its content.

## Contents

- `paper/`: `note.tex` and `note.pdf`.
- `verify/`:
  - `window_check.py`: the window identity in exact rational arithmetic for `n ≤ 3000`, positivity and the window sums, and a floating-point run to `n = 2,000,001` for the rate in Remark 4. `MUTANT=1`, `2`, `3` plant errors in the recurrence and the window; each must fail.
  - `fig_window.py`, `fig_cn.py`: the two figures, from exact rationals; each asserts what its caption says.
- `lean/`: a Lake project pinned to Lean 4.34.0 and Mathlib v4.34.0; `lean/README.md` maps results to Lean names, `CheckClaims.lean` prints their axioms, `scripts/mutants.py` runs the mutation tests.

## Reproduce

```
cd verify && python3 window_check.py && for m in 1 2 3; do MUTANT=$m python3 window_check.py | tail -1; done
python3 fig_window.py && python3 fig_cn.py
cd ../paper && latexmk -pdf note.tex
cd ../lean && lake exe cache get && lake build LeanProofs && lake env lean CheckClaims.lean
```

## Licence

The paper is released under [CC BY 4.0](../LICENSE-PAPERS), the code under the [MIT licence](../LICENSE-CODE).
