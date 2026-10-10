# Lean formalisation: catching the centroid

Lean 4.34.0 with Mathlib v4.34.0. Build with `lake exe cache get && lake build LeanProofs`, then
`lake env lean CheckClaims.lean` prints each result's axioms (only `propext`, `Classical.choice`,
`Quot.sound`). `python3 scripts/mutants.py` checks that 14 wrong variants fail.

The formalisation works with the angular density of the note: a function `ρ : ℝ → ℝ` that is continuous,
`2π`-periodic and of total mass `1` (`Dens ρ`). For a convex region with a marked point at the origin,
`ρ θ = r(θ)² / (2|K|)`, and the probability of the note is the definition

```lean
noncomputable def a (ρ : ℝ → ℝ) (θ : ℝ) : ℝ := ∫ x in θ + π / 2..θ + 3 * π / 2, ρ x
noncomputable def P (ρ : ℝ → ℝ) : ℝ := ∫ θ in (0 : ℝ)..2 * π, ρ θ * a ρ θ
```

The three classical inputs are hypotheses, in angular form:

```lean
def Grunbaum (ρ : ℝ → ℝ) : Prop := ∀ θ, ∫ x in θ..θ + π, ρ x ≤ 5 / 9
def MinkRadon (ρ : ℝ → ℝ) : Prop := ∀ θ, ρ θ ≤ 4 * ρ (θ + π)
def Stewart (ρ : ℝ → ℝ) : Prop := 2 / 3 ≤ s ρ
```

| Paper | Lean (namespace `CentroidCircle`) |
|---|---|
| Equation (2) | `a_add_pi` |
| Proposition 1 | `key` |
| Centrally symmetric regions give `1/2` | `symmetric_half` |
| Formula (3), the signed-area form, with the derivative of `b` | `signed_area`, `hasDerivAt_b` |
| Equation (4) | `integral_abs_ρo` |
| Proposition 2 | `product_bound` |
| Grünbaum gives `|b| ≤ 1/18` | `abs_b_le` |
| Theorem 1: `|P - 1/2| ≤ 1/54`, so `P ≤ 14/27` | `abs_P_sub_half_le`, `P_le_14_27` |
| Section 4: Minkowski–Radon gives Levi's `1 - s ≤ 3/5`, then `P ≤ 8/15` | `one_sub_s_le`, `P_le_8_15` |
| Lemma 1 (three lines) | `three_sectors` |
| Proposition 3: three-sided gives `s ≥ 2/3`; then `P ≤ 14/27` from Grünbaum alone | `s_ge_two_thirds`, `P_le_14_27_three_sided` |
| The hypotheses are satisfiable | `uniform_dens` |

In Lean a region is three-sided when `ρ (θ + π) ≤ ρ θ` on the three sectors `[t₀, t₁]`, `[t₂, t₀ + π]`,
`[t₁ + π, t₂ + π]`; on the other three sectors the reverse inequality then follows from periodicity.

## What is not formalised

- The passage from a convex region to its angular density: polar coordinates, Euclid III.31, and the
  identification of formula (1) with the probability in the question. In Lean, (1) is the definition of `P`.
- Grünbaum's, Stewart's and the Minkowski–Radon inequalities, quoted from the literature and taken as
  the hypotheses `Grunbaum`, `Stewart` and `MinkRadon`.
- The remark that a region close to a triangle is three-sided (sketched in the paper), and the winding-number
  remark.
