# Lean formalisation: simple unit hexagons

Lean 4.34.0 with Mathlib v4.34.0. Build with `lake exe cache get && lake build LeanProofs`, then
`lake env lean CheckClaims.lean` prints each result's axioms (only `propext`, `Classical.choice`,
`Quot.sound`). `python3 scripts/mutants.py` checks that 21 wrong variants fail.

| Paper | Lean (namespace `UnitHexagon`) | File |
|---|---|---|
| Lemma 1 (adjacent turns) | `third_edge_meets_first`, `adjacent_turns`, `angle_sum_of_turns` | `Turns.lean` |
| Lemma 2 (projection) | `projection` (convex hull form), `projection_weights` | `Projection.lean` |
| Lemma 3 (four hull edges) | `cross_at_P0`, `cross_at_P4`, `factor`, `K_neg`, `four_hull`, `no_four_unit_hull_edges`, `S_gt_pi`, `endpoint_turns_not_both_straight` | `FourHull.lean` |
| Proposition 1 (triangle), facts (a)–(d) | `left_half_unit_pair`, `same_half_le_one`, `median_lt_one`, `unit_from_Z`, `Z_le_one`, `unit_pair_opposite`, `neighbours_close`, `angle_le_pi_div_three` | `Triangle.lean` |
| Proposition 1, the invariant | `invariant_along_path`, `no_polygon_avoiding_apex`, `no_path_through_apex` | `Triangle.lean` |
| Lemma 5 (cost of a pocket), counting | `pocket_cost` | `Counting.lean` |
| Section 5, reflex counts | `reflex_count`, `hexagon_reflex_count`, `two_disjoint_pairs_impossible` | `Counting.lean` |
| Section 5, sign at `F` and at `C` | `turn_in_triangle`, `ray_order_reflex` | `Rays.lean` |
| Section 6 (sharpness) | `unit_CD`, `unit_DE`, `unit_EF`, `unit_AF`, `sign_identity`, `Fx_neg`, `Fy_bounds`, `simple_nonadjacent`, `turns`, `adjacent_meet`, `sharp` | `Sharpness.lean` |
| Section 7 (octagon counts) | `octagon_reflex_count`, `octagon_two_pockets` | `Counting.lean` |

## What is not formalised

- Lemma 4 (pockets): the Jordan-curve facts that hull contacts occur in hull order and that a pocket is a
  simple clockwise polygon.
- Lemma 5, the case k = 2: that four points in convex position bound only the convex quadrilateral.
- The passage from a polygon to the configurations above (which vertices are contacts, which edges are
  hull edges, which cross products express convexity). Each lemma is stated in the coordinates the paper
  uses, and the proof's case analysis is checked by hand.
