# Lean formalisation: what is and is not proved

Lean 4 + Mathlib, namespace `FrankCopula`, files in `LeanProofs/FrankCopula/`. Build: `lake exe cache get && lake build`;
`lake env lean CheckClaims.lean` prints the axioms of every result below (recorded in `axiom-validation.txt`). Axioms of
every result below: propext, Classical.choice, Quot.sound. No sorry, no native_decide.

## Proved
| Paper | Lean | Scope |
|---|---|---|
| Equation (2), `K = ∂C/∂u` | `hasDerivAt_C` | every `t ≠ 0`, every `u`, every `v ∈ [0,1]` |
| Proposition 3.1 | `integral_K` | `∫₀¹ K(u,v) dv = 1 - R t u` for `t ≠ 0`, `0 < u < 1` (fundamental theorem of calculus with the antiderivative `G`) |
| Lemma 3.2 | `defect`, `not_affine` | every `t ≠ 0`: the three-point defect at `u = 1/8, 1/4, 1/2` is nonzero, so `R t` agrees with no affine function on `(0,1)` |
| Lemma 4.1 | `corr_increase` | any real inner product space; explicit `ε₀ = c d n² / (c² q² + 1)`, every `0 < ε ≤ ε₀` |
| Lemma 2.1 | `cov_score`, `var_score` | any probability space, any `U, V` whose distribution functions equal the identity at the cut-points and whose joint distribution function is `C` there |

## Not formalised
- The identity `E[V | U = u] = 1 - ∫₀¹ ∂C/∂u dv` (conditional distribution of a copula and the layer-cake formula).
- The tower-property step `E[h(U)(V - 1/2)] = E[h(U)²]`, and the smoothness of `r` on `[0,1]`.
- The approximation of `u + εh(u)` by integer step functions in the proof of Theorem 1.2, and the reflection for `θ < 0`.
- Proposition 5.1 (the numerical certificate): checked by two independent interval-arithmetic programs in `../verify/`.

## Mutation tests
`scripts/mutants.toml`, run with `cd scripts && python3 mutate.py mutants.toml` (runner included): 9 mutants, all rejected,
all controls pass (`mutation-validation.log`, one diagnostic per mutant). Each is a false strengthening of a stated
result: allowing `t = 0` in `defect` and `not_affine` (where `R` is constant), dropping the `1 -` in `integral_K`,
doubling the derivative, weakening `⟪h, y⟫ > 0` to `≥ 0` or `⟪h, x⟫ = 0` to `≥ 0` (take `h = x`), and perturbing the
covariance term, the variance (`max` for `min`) and the inclusion-exclusion sign.

Pinned versions: `lean-toolchain` (Lean v4.34.0) and `lake-manifest.json` (Mathlib 5ed29652).
