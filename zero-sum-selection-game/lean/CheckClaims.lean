import LeanProofs

-- Lemma 4 (rank lemma) and Theorem 1 (dimension), for arbitrary row lengths N and quotas k
#check @ZeroSumGame.incidence_rank_bound
#print axioms ZeroSumGame.incidence_rank_bound
#check @ZeroSumGame.winning_iff_hits
#check @ZeroSumGame.winning_finite_union
#print axioms ZeroSumGame.winning_finite_union
#check @ZeroSumGame.sharp_dimension_theorem
#print axioms ZeroSumGame.sharp_dimension_theorem
#check @ZeroSumGame.square_sharp_dimension
#print axioms ZeroSumGame.square_sharp_dimension
#print axioms ZeroSumGame.winning_affine_family_dimension_bound
-- Lemma 7 (order-three criterion)
#check @ZeroSumGame.order3_criterion
#print axioms ZeroSumGame.order3_criterion
-- Lemma 8 (collisions) and its converse; Theorem 2 with distinct entries, normalised
#check @ZeroSumGame.collision
#print axioms ZeroSumGame.collision
#print axioms ZeroSumGame.coll_two
#check @ZeroSumGame.three_values
#check @ZeroSumGame.order3_distinct
#print axioms ZeroSumGame.order3_distinct
-- Proposition 9 (two-valued normal form)
#check @ZeroSumGame.two_valued
#print axioms ZeroSumGame.two_valued
