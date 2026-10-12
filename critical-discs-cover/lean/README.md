# Lean proof sources

Lean 4.34.0; Mathlib is pinned by lake-manifest.json to
5ed2965256430c3649e86755f9576b54eca72435 (v4.34.0).
SOURCE-SNAPSHOT.json records the development commit and the hash of every file. Build caches are excluded.

    lake exe cache get
    lake build LeanProofs
    lake env lean CheckClaims.lean
    python3 scripts/mutants.py

The first command fetches the pinned Mathlib cache, the second compiles the proofs, the third prints the
statements and axioms of the headline results, and the last runs the mutation tests: each plants one wrong
statement or constant and checks that the file no longer compiles.

**Scope.** The theorem is conditional on Zhou's criterion (arXiv:2609.02156) for the interior and uses
Shepp's theorem for the rim; neither is formalised, nor are the localisation and the probabilistic
estimates. Lean checks the analytic estimates that feed the two criteria.

| Paper | Lean (namespace `DiscCover`, file `Basic.lean`) |
|---|---|
| Figure 1: the lens of two unit balls contains the ball of radius `1 - s/2` about the midpoint | `lens_ball` |
| Equation (1): `(1 - s/2)² ≥ 1 - s` | `lens_sq` |
| `Σ_{n ≤ N} 1/√n ≤ 2√N` and `log(N + 1) ≤ Σ_{n ≤ N} 1/n` | `sum_inv_sqrt`, `log_le_sum_inv` |
| Section 2: `Σ_{n ≤ N} (1/n)(1 - t√(πn)) ≥ 2 log(1/t) - log π - 2`, `N = ⌊1/(πt²)⌋` | `sum_lower` |
| Section 2: `∫₀ t⁻¹ dt` diverges | `inv_not_integrable` |
| Section 3: the sliver, `1 - √(1 - x²) ≤ x²` for `|x| ≤ 1` | `sliver` |

`lens_ball` holds in any real normed space, in particular in the plane.

Every result uses only propext, Classical.choice and Quot.sound (axiom-validation.txt). The folder was
compiled in an isolated build without the development cache (build-validation.log).
