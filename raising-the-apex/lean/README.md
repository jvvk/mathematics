# Lean formalisation: raising the apex raises the Gaussian centroid

Lean 4.34.0 with Mathlib v4.34.0. Build with `lake exe cache get && lake build LeanProofs`, then
`lake env lean CheckClaims.lean` prints each result's axioms (only `propext`, `Classical.choice`,
`Quot.sound`). `python3 scripts/mutants.py` checks that 9 wrong variants fail.

| Paper | Lean (namespace `GaussianApex`) |
|---|---|
| Lemma 1: convex combinations of dilates of `K` about `D` lie in the dilate with the combined scale (so the cone `C` is convex) | `dilate_combo` |
| Lemma 2: equal-length increments of a concave function decrease to the right | `increment_anti` |
| Lemma 2: a longer interval starting no later gains strictly more (concave, strictly increasing) | `increment_gt` |
| Lemma 2: `y ↦ φ(1 - y/h₂) - φ(1 - y/h₁)` is strictly increasing on `(0, h₁)` | `ratio_strictMono` |
| Chebyshev's integral inequality for any finite measure on `ℝ`, and its strict form | `double_integral`, `chebyshev`, `chebyshev_strict` |
| Mass added above the old range raises the mean | `mean_mix` |

## What is not formalised

- Prékopa's theorem (Acta Sci. Math. 34 (1973), Theorem 6), which makes `log F` concave given Lemma 1.
- The factorisation of the Gaussian into horizontal and vertical parts, the resulting height densities
  `w(y) F(1 - y/h)`, and the strict increase of `F` (nested sections of growing volume).
