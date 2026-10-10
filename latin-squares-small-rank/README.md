# Latin squares of small rank

<!-- visual:start -->
<p align="center"><img src="https://raw.githubusercontent.com/jvvk/jvvk/e44d1155b2eafea7d99e6fa386488b981dc7f3e3/assets/latin-rank.svg" width="760" alt="Latin squares of small rank"></p>

<p align="center"><b>Every Latin square of order n has rank at least 1 + 3(n−1)/(n+1), so at least 4 from n = 5 on; the least ranks up to order 8 are 1, 2, 3, 3, 5, 4, 6, 4.</b><br><sub>Partial progress on an open question · bound and r(6), r(8) in Lean</sub></p>

<p align="center"><sub><a href="paper">paper</a> · <a href="lean">Lean proof</a> · <a href="verify">code</a> · <a href="../">all results</a></sub></p>
<!-- visual:end -->

Let `r(n)` be the least real rank of an `n × n` Latin square with entries `1, …, n`. Philip Weiss asked on MathOverflow ([question 515241](https://mathoverflow.net/q/515241)) whether `r(n)` can stay bounded, and observed that the exclusive-or square gives `r(2^k) ≤ k + 1`.

Every Latin square of order `n` has rank at least `1 + 3(n−1)/(n+1)`, with strict inequality for odd `n` (Theorem 1), so `r(n) ≥ 4` for all `n ≥ 5`. The proof writes the centred square as inner products of `n` row points and `n` column points in `R^d`, `d = rank − 1`, and applies Cauchy–Schwarz once per row. The exact values for `n ≤ 8` are `1, 2, 3, 3, 5, 4, 6, 4`: no Latin square of order 5 is singular. Whether `r(n)` is unbounded stays open; the bound cannot pass 4.

Preprint v1, 10 October 2026, not peer reviewed. Theorem 1 with its strict form, Corollary 2, and `r(4) = 3`, `r(6) = 4`, `r(8) = 4` are formally verified in Lean 4 (`lean/`, standard axioms only). `r(5) = 5` and `r(7) = 6` rest on an exhaustive computation over McKay's isotopy representatives with an exact modular certificate. The author used AI tools (Claude, Anthropic) in this work, as described in the paper's acknowledgement, and is responsible for its content.

## Contents

- `paper/`: `note.tex`, `note.pdf`, and `make_figs.py`, which computes the planar factorisation of Figure 1 and asserts every number in its caption.
- `verify/`:
  - `certify_minrank.py`: for `n = 4, …, 7`, the rank modulo `2^31 − 1` of every isotopy representative under every assignment of the values `1, …, n` (rank mod p ≤ rank over Q, so the minimum is an exact lower bound), and an exact witness. `--mutant` computes ranks mod 3 and must fail. `certify_n7.txt` is the output for `n = 7` (65 s).
  - `fetch_data.py`: downloads B. D. McKay's isotopy-class representatives (2, 2, 22, 564 classes) into `data/` and checks their SHA-256 hashes. The files are not redistributed here.
  - `factorise.py`: the integer factorisations `V = A B` used by the Lean witnesses.
- `lean/`: a Lake project pinned to Lean 4.34.0 and Mathlib v4.34.0; `lean/README.md` maps results to Lean names, `CheckClaims.lean` prints their axioms, `scripts/mutants.py` runs the mutation tests.

## Reproduce

```
cd verify && python3 fetch_data.py && python3 certify_minrank.py 4 5 6 && python3 certify_minrank.py 7
cd ../paper && python3 make_figs.py && latexmk -pdf note.tex
cd ../lean && lake exe cache get && lake build LeanProofs && lake env lean CheckClaims.lean
```

Python needs `numpy` and `sympy`.

## Licence

The paper is released under [CC BY 4.0](../LICENSE-PAPERS), the code under the [MIT licence](../LICENSE-CODE).
