# Permutations with no whole-number averages

<!-- visual:start -->
<p align="center"><img src="https://raw.githubusercontent.com/jvvk/jvvk/96d4523a32eccaa841688a232aca9f7bd41e2cfe/assets/good-perm.svg" width="760" alt="Permutations with no whole-number averages"></p>

<p align="center"><b>If no proper block of a permutation of 1..n averages to a whole number, then n = 2ᵐ − 1; the asker's example works exactly when n is prime, and n = 15, 63 have none.</b><br><sub>Part of a question answered · theorems in Lean; n ≤ 63 by two searches</sub></p>

<p align="center"><sub><a href="paper">paper</a> · <a href="lean">Lean proof</a> · <a href="verify">code</a> · <a href="../">all results</a></sub></p>
<!-- visual:end -->

Call a permutation of `1, …, n` *good* if no block of consecutive entries, of length at least 2 and other than the whole permutation, has an integer average. Philip Weiss asked on MathOverflow ([question 514690](https://mathoverflow.net/q/514690)) whether, for odd `n`, good permutations exist exactly when `n` is a Mersenne prime. Sergiu Alexandru Bîsceanu's [answer](https://mathoverflow.net/a/514702), building on a comment by te4, shows that `n` must be `2^m − 1` (Theorem 1). Whether a composite `2^m − 1` can have a good permutation is open.

This note adds:

- **Theorem 2.** For `n = 2^m − 1`, the asker's permutation `1, n−1, n, n−3, n−2, …, 2, 3` has an integer-average block exactly at the prefixes whose length divides `n`. So it is good if and only if `n` is prime. The proof reads off every block average from the closed form `a_t = n + 2 − t − (−1)^t`.
- **Theorem 3.** For `n = 7` and `31` there are exactly four good permutations (the asker's, its reverse, its complement and the reverse of the complement); for the composite `n = 15` and `63` there are none. The search for `63` uses the structure in Bîsceanu's proof (Corollary 5: `a_q = q` and positions `i`, `i + q` hold values `q` apart), which halves the search.

Preprint v1, 10 October 2026, not peer reviewed. Theorem 1 (with te4's congruence), Corollary 5 and Theorem 2 are formally verified in Lean 4 (`lean/`, standard axioms only); Theorem 3 is computational. The author used AI tools (Claude, Anthropic) in this work, as described in the paper's acknowledgement, and is responsible for its content.

## Contents

- `paper/`: `note.tex` and `note.pdf`; `figs/` holds the TikZ figure data written by `verify/figs.py`.
- `verify/`:
  - `check.py`: checks Theorem 2 directly for `n ≤ 2047`; compiles and runs `half_search.c` (the reduced search) for `n = 7, 15, 31, 63` and `plain_count.c` (no structural assumption) for every odd `n ≤ 41`, and asserts every count and node count in Table 1. Runs in about 3 minutes. `MUTANT=1` builds the reduced search with a planted error (block lengths dividing `n` skipped); it must print `FAIL`.
  - `half_search.c`, `plain_count.c`: the two searches.
  - `figs.py`: the figures; asserts the bad blocks for `n = 15` and `31` shown in Fig. 2.
- `lean/`: a Lake project pinned to Lean 4.34.0 and Mathlib v4.34.0; `lean/README.md` maps results to Lean names, `CheckClaims.lean` prints their axioms, `scripts/mutants.py` runs the mutation tests.

## Reproduce

```
cd verify && python3 check.py && MUTANT=1 python3 check.py | tail -1 && python3 figs.py
cd ../paper && latexmk -pdf note.tex
cd ../lean && lake exe cache get && lake build LeanProofs && lake env lean CheckClaims.lean
```

`check.py` needs a C compiler (`cc`).

## Licence

The paper is released under [CC BY 4.0](../LICENSE-PAPERS), the code under the [MIT licence](../LICENSE-CODE).
