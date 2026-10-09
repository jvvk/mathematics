# Monotonicity of a ratio of complete homogeneous symmetric polynomials

Let `H_i(x) = h_ℓ(1, …, 1, x, …, x)` be the complete homogeneous symmetric polynomial of degree `ℓ` in `n` variables, with `i` of them equal to `x` and the rest equal to `1`. Rachid Ait-Haddou conjectured on MathOverflow (question 467261, 2024) that `Ψ_{i,n} = H_i² / (H_{i+1} H_{i-1})` is strictly increasing on `(1, ∞)` for `2 ≤ i ≤ n - 2`. The note proves it for every `ℓ ≥ 1` and every `1 ≤ i ≤ n - 1`. Treating `i` as a real variable `t`, the logarithmic derivative of `Ψ_{i,n}` is a positive multiple of a second difference in `t` of `P_{ℓ-1}/P_ℓ`, where the `P_ℓ` form a Meixner family; that ratio is convex because the zeros interlace.

Preprint v1, 9 October 2026, not peer reviewed. Theorem 1 and the lemmas of its proof are also formally verified in Lean 4 (`lean/`, standard axioms only). The exposition has not yet been independently reviewed. The author used an AI tool (Claude, Anthropic) in this work, as described in the paper's acknowledgements, and is responsible for its content.

## Contents

- `paper/`: `paper.tex`, `paper.pdf`, and `fig_data.py` (the data of Figure 1).
- `verify/verify_paper.py`: from the definitions alone, checks Lemmas 1 to 5 and Proposition 3 in exact arithmetic for small `n` and `ℓ`, Theorem 1 on rational grids, the example `ℓ = 1`, the symmetry `Ψ_{i,n}(1/x) = Ψ_{n-i,n}(x)`, the Meixner identification and the data of Figure 1 (read from `paper.tex`); six planted mutants are killed.
- `lean/`: a Lake project pinned to Lean 4.34.0 and Mathlib v4.34.0. `lean/README.md` maps the results to Lean names; `SOURCE-SNAPSHOT.json` records the development commit and file hashes; `mutants.sh` plants eleven wrong changes, each rejected.

## Reproduce

```
cd verify
python3 verify_paper.py                 # needs sympy and mpmath; under a minute
cd ../paper && latexmk -pdf paper.tex
cd ../lean && lake exe cache get && lake build   # builds every module and prints the axiom audit
./mutants.sh                                     # eleven mutants, each rejected
```

## Licence

The paper is released under [CC BY 4.0](../LICENSE-PAPERS), the code under the [MIT licence](../LICENSE-CODE).
