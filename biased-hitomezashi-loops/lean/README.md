# Lean formalisation: biased hitomezashi loop density

Lean 4.34.0, Mathlib v4.34.0 (pinned in `lake-manifest.json`), namespace `HitomezashiBiased`, files in
`LeanProofs/HitomezashiBiased/`. Standard axioms only (`propext`, `Classical.choice`, `Quot.sound`); see
`axiom-validation.txt`, written by `lake env lean CheckClaims.lean` in an isolated build.

| Paper | Status | Lean |
|---|---|---|
| Lemma 2.1 (labels along a stitch walk) | formalised | `Parity.lean`: `parity_along`, `vertical_label`, `horizontal_label` |
| Theorem 2.2 (Pete's bijection) | cited (Pete 2008; Defant-Kravitz Thm 3.1); our reading checked on all 7 × 7 loops | `../verify/per_loop.py` |
| Lemma 2.3 (zeros of a label word) | formalised | `LabelWord.lean`: `zeros_closed`, `label_word` |
| Corollary 2.5, Proposition 3.1 | paper proof only | sanity: `../verify/monte_carlo.py`, `../verify/closed_form.py` |
| Proposition 4.1 (continued fraction theorem) | cited (Flajolet 1980; Flajolet-Sedgewick Prop. V.3(ii)) | |
| Lemma 4.2 (evaluation at z = 1) | paper proof only | |
| Lemma 4.3 (Casoratian, exact height) | formalised | `Continuant.lean`: `casoratian`, `excHeight_eq` |
| Lemma 4.4 (closed-form continuants) | formalised | `Continuant.lean`: `Q_alt` |
| Proposition 4.5 (X_k) | formalised | `Continuant.lean`: `X_even`, `X_odd` |
| cot and csc² series | formalised (from Mathlib `cot_series_rep'`, term-wise differentiation) | `Series.lean`: `hasSum_K`, `hasSum_T` |
| Theorem 1.1, the series identity | formalised | `Series.lean`: `hasSum_density` (p ≠ 1/2), `hasSum_density_half` |
| Theorem 6.1 (strict monotonicity, quantitative minimum) | paper proof only | exact polynomial certificate: `../verify/extensions.py` |
| Theorem 6.2 (two biases, truncation error) | paper proof only | `../verify/two_parameter.py`, `../verify/extensions.py` |

What the Lean proves for Theorem 1.1: given the density as the series over heights that Sections 2 to 4 derive,
the series sums to the closed form. The probabilistic limiting-density argument and the identification of loops
with weighted Dyck paths are paper proofs.

## Build and check

```
lake exe cache get && lake build LeanProofs && lake env lean CheckClaims.lean
python3 -I scripts/mutate.py scripts/mutants.toml
```

`scripts/mutants.toml` holds 15 planted wrong changes (wrong constants in the density, shifted continuants, wrong
label parities); each must make Lean report an error. `SOURCE-SNAPSHOT.json` records the source commit in the
author's working repository and the hash of every file.
