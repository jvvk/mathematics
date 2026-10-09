# Counting cycles in a Sylow 2-subgroup

<!-- visual:start -->
<p align="center"><img src="https://raw.githubusercontent.com/jvvk/jvvk/c7403d6bbbc7106e1780d8c34833854afcb0116f/assets/sylow.svg" width="760" alt="Counting cycles in a Sylow 2-subgroup"></p>

<p align="center"><b>The two factors Stanley observed are irreducible over the rationals at every level.</b><br><sub>Open problem settled · formally verified in Lean 4</sub></p>

<p align="center"><sub><a href="paper">paper</a> · <a href="lean">Lean proof</a> · <a href="verify">code</a> · <a href="../">all results</a></sub></p>
<!-- visual:end -->

Count the permutations in a Sylow 2-subgroup of the symmetric group on `2^n` points by their number of cycles. Richard Stanley observed on MathOverflow ([question 489315](https://mathoverflow.net/q/489315)) that a closely related polynomial, after adding a power of 2, splits into two factors of equal degree that appear to be irreducible. Darij Grinberg and Max Alekseyev proved the factorization there; irreducibility was left open.

Both factors are irreducible over `Q` for every `n` (Theorem 1 and its corollary). The recurrence printed in the question is one index off from the Sylow polynomials. The paper treats both families, and the same proof covers each. After scaling, both are iterates of the triangular-number map `T(x) = x(x+1)/2`. The factorization is a difference of two squares, `T(T(z)) + 1 = (z² − z + 2)(z² + 3z + 4)/8`. Irreducibility follows modulo 5: the critical orbit of `T` there is `3 → 1 → 1`, both factors take non-square values along it, and the quadratic case of Capelli's lemma applies at every step. The analogous question for odd primes stays open; the paper reduces it to iterates of `(x^p + (p−1)x)/p` and records small cases.

Preprint v1, 9 October 2026, not peer reviewed. Every algebraic statement (the composition lemma with its norm computation, both factorizations, the coefficient agreement, irreducibility over `F_5`, `Z` and `Q` for every `n`) is formally verified in Lean 4 (`lean/`, standard axioms only). The identification of the recurrence with the cycle count is the classical wreath-product formula, proved in the paper and checked by listing the group for `n ≤ 4`. The author used AI tools (Codex, OpenAI; Claude, Anthropic) in this work, as described in the paper's acknowledgement, and is responsible for its content.

## Contents

- `paper/`: `note.tex` and `note.pdf`.
- `lean/`: a Lake project pinned to Lean 4.34.0 and Mathlib v4.34.0; `lean/README.md` maps results to Lean names, `CheckClaims.lean` prints their axioms, `scripts/mutants.py` runs the mutation tests.
- `verify/`:
  - `recheck.py`: an independent check from the definitions, sharing no code with the other programs or the Lean. It lists `G_{2^n}` for `n ≤ 4` and counts cycles, showing that the printed `f_n` is not the Sylow polynomial for `n ≥ 2`. It checks the normalisation, both factorizations up to `n = 8` and the coefficient agreement, irreducibility modulo 5 up to degree 128, the composition lemma in both directions on random examples, the critical-orbit table, controls modulo 3 and 7, and the odd-prime normalisation with factor degrees. `--quick` gives a short run; `recheck-full.log` is the full run.
  - `codex_verify.py`: the first finite check (Frobenius/gcd irreducibility test modulo 5 for the printed family, `n ≤ 8`), with `codex_verification.json`.

## Reproduce

```
cd verify
python3 recheck.py --quick
cd ../paper && latexmk -pdf note.tex
cd ../lean && lake exe cache get && lake build LeanProofs && lake env lean CheckClaims.lean
```

Python needs `sympy`.

## Licence

The paper is released under [CC BY 4.0](../LICENSE-PAPERS), the code under the [MIT licence](../LICENSE-CODE).
