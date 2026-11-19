# Monotonicity of a ratio of complete homogeneous symmetric polynomials

<!-- visual:start -->
<p align="center"><img src="https://raw.githubusercontent.com/jvvk/jvvk/c7403d6bbbc7106e1780d8c34833854afcb0116f/assets/symmetric-ratio.svg" width="760" alt="A ratio of symmetric polynomials"></p>

<p align="center"><b>Ait-Haddou's ratio of complete homogeneous symmetric polynomials increases, for every degree and position.</b><br><sub>Independent proof of a result first proved by Sra · formally verified in Lean 4</sub></p>

<p align="center"><sub><a href="paper">paper</a> · <a href="lean">Lean proof</a> · <a href="verify">code</a> · <a href="../">all results</a></sub></p>
<!-- visual:end -->

Let `H_i(x) = h_ℓ(1, …, 1, x, …, x)` be the complete homogeneous symmetric polynomial of degree `ℓ` in `n` variables, with `i` of them equal to `x` and the rest equal to `1`. Rachid Ait-Haddou conjectured on MathOverflow (question 467261, 2024) that `Ψ_{i,n} = H_i² / (H_{i+1} H_{i-1})` is strictly increasing on `(1, ∞)` for `2 ≤ i ≤ n - 2`. Suvrit Sra proved it, for every `ℓ ≥ 1` and every `1 ≤ i ≤ n - 1`, in a preprint released on 7 October 2026 ([Monotonicity of Turán-ratios of symmetric polynomials](https://suvrit.github.io/papers/sym-turan/), Corollary 1.2, the one-row case of a theorem on Schur polynomials). This note, posted as a MathOverflow answer a few hours later the same day, gives an independent proof; Sra's preprint has priority. Treating `i` as a real variable `t`, the logarithmic derivative of `Ψ_{i,n}` is a positive multiple of a second difference in `t` of `P_{ℓ-1}/P_ℓ`, where the `P_ℓ` form a Meixner family; that ratio is convex because the zeros interlace.

Preprint v2, 19 November 2026 (v1: 9 October 2026), not peer reviewed. **Version 2** credits Sra's earlier proof and Koepf's 1997 derivative rule for Meixner polynomials (a case of which is Lemma 2), corrects the domain stated in Remark 1, and moves the Lean mutants to the house harness; the mathematics is unchanged. Theorem 1 and the lemmas of its proof are also formally verified in Lean 4 (`lean/`, standard axioms only). The exposition has not yet been independently reviewed. The author used an AI tool (Claude, Anthropic) in this work, as described in the paper's acknowledgements, and is responsible for its content.

## Contents

- `paper/`: `paper.tex`, `paper.pdf`, and `fig_data.py` (the data of Figure 1).
- `verify/verify_paper.py`: from the definitions alone, checks for small integer `n` and `ℓ` the polynomial identities of Lemmas 1 to 5 and Proposition 3 in exact arithmetic and the statements about zeros (reality, interlacing, signs of the weights) numerically at high precision, Theorem 1 on rational grids, the example `ℓ = 1`, the symmetry `Ψ_{i,n}(1/x) = Ψ_{n-i,n}(x)`, the Meixner identification and the data of Figure 1 (read from `paper.tex`); six planted mutants are killed.
- `lean/`: a Lake project pinned to Lean 4.34.0 and Mathlib v4.34.0. `lean/README.md` maps the results to Lean names; `SOURCE-SNAPSHOT.json` records the development commit and file hashes; `scripts/mutants.toml` plants eleven wrong changes, each rejected with a Lean error located in the mutated file (`mutation-validation.log`).

## Reproduce

```
cd verify
python3 verify_paper.py                 # needs sympy and mpmath; under a minute
cd ../paper && latexmk -pdf paper.tex
cd ../lean && lake exe cache get && lake build   # builds every module and prints the axiom audit
python3 -I scripts/mutate.py scripts/mutants.toml   # eleven mutants, each rejected
```

## Licence

The paper is released under [CC BY 4.0](../LICENSE-PAPERS), the code under the [MIT licence](../LICENSE-CODE).
