import LeanProofs.FrankCopula.NotAffine
import LeanProofs.FrankCopula.Regression
import LeanProofs.FrankCopula.Variation
import LeanProofs.FrankCopula.Ordinal

/-!
# Discretising a Frank copula can inflate correlation (disproof of Barbiero's conjecture)

Formalised:
* `FrankCopula.hasDerivAt_C`: `∂C/∂u = K` (the conditional distribution function).
* `FrankCopula.integral_K`: `∫₀¹ K(u, v) dv = 1 - R t u`, so `E[V | U = u] = R t u` (closed form).
* `FrankCopula.not_affine`: for every `t ≠ 0`, `R t` agrees with no affine function on `(0, 1)`.
* `FrankCopula.corr_increase`: in an inner product space, `⟪h, x⟫ = 0`, `⟪h, y⟫ > 0` give an explicit `ε > 0`
  with `corr(x + ε h, y) > corr(x, y)`.
* `FrankCopula.cov_score`, `FrankCopula.var_score`: covariance and variance of integer-score ordinal variables,
  `∑∑ (C(aₖ, bₗ) - aₖ bₗ)` and `∑∑ (min(aₖ, aₗ) - aₖ aₗ)`.

Not formalised (cited): the layer-cake identity `E[V | U = u] = 1 - ∫₀¹ ∂ᵤC dv`; the tower-property step
`⟪h, y⟫ = ‖h‖²`; the approximation of `id + ε h` by integer step functions; the numerical certificate for the
15-category example (Arb ball arithmetic in `verify/`, with an independent recheck).
-/
