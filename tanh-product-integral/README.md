# An integral of hyperbolic tangents: residues, characters and the conductors that occur

<!-- visual:start -->
<p align="center"><img src="https://raw.githubusercontent.com/jvvk/jvvk/4eeb87187c785d1e18b5886036dccc97d49974c5/assets/tanh-product.svg" width="760" alt="An integral of hyperbolic tangents"></p>

<p align="center"><b>The integral of tanh(x)tanh(2x)⋯tanh(nx)/x² reduces, for odd n, to logarithms and L′(−1) values with explicit coefficients; a cotangent symmetry explains which conductors appear.</b><br><sub>Answers an open Math.SE question · residue steps formally verified in Lean · analytic steps cited and checked</sub></p>

<p align="center"><sub><a href="paper">paper</a> · <a href="lean">Lean proof</a> · <a href="verify">code</a> · <a href="../">all results</a></sub></p>
<!-- visual:end -->

For `n ≥ 2` let `I_n = ∫₀^∞ x⁻² tanh(x) tanh(2x) ⋯ tanh(nx) dx`. On [Mathematics Stack Exchange 5150767](https://math.stackexchange.com/q/5150767) (Michael Smith, 2026) it was observed that for odd `n` the value is a rational combination of logarithms and values `L′(−1, ψ)` of even Dirichlet characters, with coefficients and conductors that look patternless, and asked for a general reduction with its coefficients.

**Theorem 1.** `P_n(q) = ∏ (1 − q^k)/(1 + q^k)` has simple poles exactly at the primitive `2m`-th roots of unity `ζ = e^{iπj/m}` with `⌊n/m⌋` odd. Writing `n = (2e+1)m + ρ`, the residue is

`(2/m) · 4^e e!² / (2e+1)! · (−i)^{m−1} ε_m(j) · ∏_{k ≤ ρ} i cot(π j k / 2m)`.

**Theorem 3.** Expanding these residues in characters gives the coefficient of every `L′(−1, ψ)` in `I_n` as a finite character sum, and the logarithms explicitly.

**Corollary 4.** A product of `ρ` of these cotangents is `±` the product of `m − 1 − ρ` of them, so only `ρ′ = min(ρ, m − 1 − ρ)` matters, and families with `ρ′ = 0` bring no new conductor. This accounts for every conductor in the question's lists: for example `16` vanishes at `n = 15` because the family `m = 8` then has `ρ = 7 = m − 1`.

The question's `L′(2)/L(2)` form has no Euler constant or `ln 2π` because those come multiplied by `Σ K_ψ L(−1, ψ) = 0`. What is not done is a closed form for the cotangent character sums themselves.

Preprint v1, 10 October 2026, not peer reviewed and not yet independently reviewed. The finite trigonometric identities behind Theorem 1 (the constant, the factor identity, the tangent pairings, the full-period product, the assembled product over all `k ≤ n`), Corollary 4 and the inversion rule are formally verified in Lean 4 (`lean/`, standard axioms only). The analytic steps are cited (Montgomery and Vaughan, Theorem 9.12 and Corollary 10.9; the Mellin relation from the question) and checked numerically, with an independent recheck. The author used AI tools (Claude, Anthropic) in this work, as described in the paper's acknowledgement, and is responsible for its content.

## Contents

- `paper/`: `note.tex`, `note.pdf`, the figure `fig_poles.tex` and its generator `make_fig.py`.
- `lean/`: a Lake project pinned to Lean 4.34.0 and Mathlib v4.34.0; `lean/README.md` maps results to Lean names, `CheckClaims.lean` prints their axioms, `scripts/mutants.py` runs 10 mutation tests.
- `verify/`:
  - `residues.py`: the residue formula against the exact power series for `n ≤ 15`.
  - `characters.py`: Lemma 2 for all moduli up to 40, and Theorem 3 against quadrature for `n ≤ 11`.
  - `conductors.py`: the cotangent symmetry and the conductor sets for odd `n ≤ 15`.
  - `check.py`: seven claims (residues, inversion, Lemma 2, Theorem 3 and the quoted coefficients, Table 1 and the conductor rule, the `L′(2)/L(2)` weights, the question's closed forms), each with a mutant that is caught.
  - `recheck/recheck.py`: an independent program that uses neither the residues nor Lemma 2; it expands `c_n` over one period in the basis `ψ(N/h)[h | N]` and recovers the conductors and coefficients for `n = 5, 7, 9`.

## Reproduce

```
cd verify && python3 check.py                   # about 1 minute; needs mpmath and sympy
cd recheck && python3 recheck.py                # about 10 seconds; needs numpy
cd ../../paper && latexmk -pdf note.tex
cd ../lean && lake exe cache get && lake build LeanProofs && lake env lean CheckClaims.lean
```

## Licence

The paper is released under [CC BY 4.0](../LICENSE-PAPERS), the code under the [MIT licence](../LICENSE-CODE).
