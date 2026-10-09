import LeanProofs.UnitHexagon.Turns
import LeanProofs.UnitHexagon.Projection
import LeanProofs.UnitHexagon.FourHull
import LeanProofs.UnitHexagon.Triangle
import LeanProofs.UnitHexagon.Counting
import LeanProofs.UnitHexagon.Rays
import LeanProofs.UnitHexagon.Sharpness

/-!
# Simple unit hexagons have diameter greater than `√2` (MO 481323)

What is formalised, following the paper's proof:
* `third_edge_meets_first`, `adjacent_turns`, `angle_sum_of_turns`: the adjacent-turn lemma;
* `projection`: the four-point projection lemma, in any real inner product space;
* `four_hull`, `no_four_unit_hull_edges`, `S_gt_pi`, `endpoint_turns_not_both_straight`: four consecutive
  unit hull edges;
* `unit_pair_opposite`, `neighbours_close`, `unit_from_Z`, `angle_le_pi_div_three`,
  `no_polygon_avoiding_apex`, `no_path_through_apex`: the triangle lemma;
* `pocket_cost`, `hexagon_reflex_count`, `octagon_reflex_count`, `two_disjoint_pairs_impossible`,
  `octagon_two_pockets`: angle counting;
* `turn_in_triangle`, `ray_order_reflex`: the two sign lemmas of the two-reflex case;
* `simple_nonadjacent`, `turns`, `adjacent_meet`, unit-edge lemmas and `sharp`: the sharpness family.

Not formalised: the planar-topology facts of the pocket lemma (hull contacts occur in hull
order; each pocket is a simple clockwise polygon), and the assembly of the case analysis.
-/
