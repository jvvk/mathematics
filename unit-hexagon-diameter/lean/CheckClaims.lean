import LeanProofs

open UnitHexagon
-- Lemma 1 (adjacent turns)
#check @third_edge_meets_first
#print axioms third_edge_meets_first
#print axioms adjacent_turns
#print axioms angle_sum_of_turns
-- Lemma 2 (projection)
#check @projection
#print axioms projection
-- Lemma 3 (four hull edges)
#check @four_hull
#print axioms four_hull
#print axioms no_four_unit_hull_edges
#print axioms S_gt_pi
#print axioms endpoint_turns_not_both_straight
-- Proposition 1 (triangle with two unit sides)
#check @unit_pair_opposite
#print axioms unit_pair_opposite
#print axioms neighbours_close
#print axioms unit_from_Z
#print axioms angle_le_pi_div_three
#print axioms no_polygon_avoiding_apex
#print axioms no_path_through_apex
-- Lemma 5 and the counting of Sections 5 and 7
#print axioms pocket_cost
#print axioms hexagon_reflex_count
#print axioms two_disjoint_pairs_impossible
#print axioms octagon_reflex_count
#print axioms octagon_two_pockets
-- Section 5, sign lemmas
#print axioms turn_in_triangle
#print axioms ray_order_reflex
-- Section 6 (sharpness and containment thresholds)
#print axioms simple_nonadjacent
#print axioms turns
#print axioms adjacent_meet
#check @sharp
#print axioms sharp
