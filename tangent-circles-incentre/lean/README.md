# Lean formalisation: three tangent circles

Lean 4.34.0 with Mathlib v4.34.0. Build with `lake exe cache get && lake build LeanProofs`, then
`lake env lean CheckClaims.lean` prints each result's axioms (only `propext`, `Classical.choice`,
`Quot.sound`). `python3 scripts/mutants.py` checks that 17 wrong variants fail.

| Paper | Lean (namespace `TangentCircles`) | File |
|---|---|---|
| Section 3, the chords | `halfchord_A`, `halfchord_B`, `midpoints_sum`, `product_identity`, `tidy`, `a_div` | `Chords.lean` |
| Section 3, the substitution (4) and the integral `π` | `hasDerivAt_u`, `integral_g` | `Integral.lean` |
| Theorem 2, density (2) and its distribution function | `density_form`, `cdf`, `half_mass`, `half`, `tail` | `Crossing.lean` |
| Lemma 1 (tangent lengths) and Theorem 1 | `tangent_length`, `half_angles`, `rho_sq_lt`, `miss_side`, `conclusion` | `Incircle.lean` |
| Remark (inner arcs) | `inner_arcs` | `Incircle.lean` |
| Theorem 3 (sphere) and the lunes | `fold_element`, `fold_pair`, `element_change`, `lune`, `lune_fraction` | `Sphere.lean` |

`integral_g` is the improper integral of `cos η / √(cos² s - sin² η)` over `|η| < π/2 - |s|`, proved via
the antiderivative `arcsin (sin η / cos s)` and Mathlib's `integrableOn_deriv_of_nonneg`. The half-angle
identity takes the inradius from Heron's formula, `ρ²(a + b + c) = abc`.

## What is not formalised

- The change of variables (3) from pairs of points to lines, as a statement about measures.
- The plane geometry of Lemmas 1 and 2: the sectors seen from the incentre tile the turn, and a side
  misses the incentre exactly when its crossing point lies beyond it.
