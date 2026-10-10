# Lean formalisation: boomerangs in Pólya's orchard

Lean 4.34.0 with Mathlib v4.34.0. Build with `lake exe cache get && lake build LeanProofs`, then
`lake env lean CheckClaims.lean` prints each result's axioms (only `propext`, `Classical.choice`,
`Quot.sound`, or fewer). `python3 scripts/mutants.py` checks that 11 wrong variants fail.

| Paper | Lean (namespace `OrchardArcs`) |
|---|---|
| Theorem 1: the smaller root `t₀` of `K t² − 2A t + r(1−r)` | `t0_root`, `t0_pos`, `t0_le`, `disc_nonneg` |
| Theorem 1: the starting condition `x(1−r) ≥ r` in half-angle form | `start_condition`, `height_identity` |
| Theorem 1: the passage (box and strip clear of all discs; the arc stays in `r ≤ x ≤ 1−r`) | `rise_clear`, `corridor_clear`, `arc_in_corridor` |
| Theorem 1: the estimate `> 4/r − 10` | `sqrt_lower`, `lower_value` |
| Lemma 2 (corridor lemma) | `corridor_lemma` |
| Lemma 3 (Farey directions), from `\|u\| + \|w\| > Q` | `farey_product`, `farey_angle` |
| Theorem 2, large `a`: the offset `≤ 0.29 r` | `minkowski_offset` |
| Theorem 2, middle `a`: the conditions on `ε_m` | `eps_sq`, `eps_cos`, `eps_tan`, `eps_le`, `eps_lt_half_pi` |
| Theorem 2: the three ranges give `≤ 28/r²` | `middle_bound`, `small_bound`, `large_bound` |

## What is not formalised

Minkowski's convex body theorem and Pick's theorem (that consecutive primitive directions have `det = ±1`) are cited.
The elementary circle geometry that links an arc to its reach and to the interval of directions of its second half
is in the paper. The searches and the certified arcs are computations in `verify/`.
