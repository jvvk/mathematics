# Lean formalisation: why the sphere beats the ball

Lean 4.34.0 with Mathlib v4.34.0. Build with `lake exe cache get && lake build LeanProofs`, then
`lake env lean CheckClaims.lean` prints each result's axioms (only `propext`, `Classical.choice`,
`Quot.sound`). `python3 scripts/mutants.py` checks that 10 wrong variants fail.

`obtuse u v w` is the integral (1) of the note: the obtuse probability at the vertex of radius `w` with opposite
radii `u, v`, written as `∫ max 0 (min (M/(2uv)) ((K - (M - w)²)/(8uvw))) dM` over `[|u - v|, u + v]`,
`K = u² + v² - w²`. `acute a b c = 1 - obtuse b c a - obtuse a c b - obtuse a b c`.

| Paper | Lean (namespace `AcuteRadial`) |
|---|---|
| Lemma 1: the angle at `W` is obtuse iff `(U + V)·W > U·V + abs(W)²` | `obtuse_iff` |
| A uniform point of `[-L, L]` exceeds `T` with probability `max 0 (min 1 ((L - T)/(2L)))` | `uniform_tail` |
| The integrand of (1) is the density of `M` times that probability | `integrand_eq` |
| `p_C = 1/2 - c²/(3ab)`, `p_B = (a - b)/(2a) + c²/(6ab)`, `p_A = h³/(6abc)` for every `a ≥ b ≥ c > 0` | `obtuseC`, `obtuseB`, `obtuseA` |
| Theorem 1: the formula | `acute_formula` |
| Theorem 1: `P ≤ 1/2`, strict when `a > b`, equal to `1/2` on one sphere (via `G` increasing) | `acute_le_half`, `acute_lt_half`, `acute_sphere`, `G_strictMono` |
| Corollary 1, one radius zero: `b/(2a) ≤ 1/2`, equality iff `a = b` | `centre_vertex` |
| Section 5: the two mixture polynomials, `F₂'(0) = 3/4`, `F₂(1/10) = 243/800`, `F₃ < 1/2` | `mixture2`, `mixture2_deriv`, `mixture2_tenth`, `mixture3` |

## What is not formalised

- Archimedes' hat-box theorem and the conditioning on `U, V` that turns it into the integral (1).
- The decomposition of a rotationally invariant law into an independent radius and uniform direction, and the
  conditioning argument of Corollary 1.
- That a triangle has at most one obtuse angle and right angles have probability zero (used to write
  `P = 1 - p_A - p_B - p_C`).
