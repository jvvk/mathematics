import LeanProofs

open BrokenStick
-- the map (2) from the Gram matrix to the squared lengths, and its determinant (dq = 2^(n(n-1)/2) dG)
#check @gramMap3_apply
#print axioms gramMap3_apply
#check @det_gramMap3
#print axioms det_gramMap3
#print axioms det_gramMap2
#check @edges_minus_offdiag
#print axioms edges_minus_offdiag
-- identity (4): sum of t_e l_e^2 = tr(L_t G)
#check @trace_identity3
#print axioms trace_identity3
#print axioms trace_identity2
-- spanning trees, the matrix-tree theorem, and the duality (6)
#check @card_spanning_trees
#print axioms card_spanning_trees
#check @det_lap3
#print axioms det_lap3
#print axioms det_lap2
#check @duality3
#print axioms duality3
#print axioms duality2
-- the substitution t = 1/(4 beta) and the collected powers
#check @kirchhoff3_quarter_inv
#print axioms kirchhoff3_quarter_inv
#print axioms schwinger_jacobian
#print axioms inv_sqrt_quarter_inv
#print axioms four_pow_half
#check @homogeneity_degree
#print axioms homogeneity_degree
-- the constants, the Feynman normalisation, and the triangle
#check @C2_eq
#print axioms C2_eq
#check @C3_eq
#print axioms C3_eq
#check @C3_feynman
#print axioms C3_feynman
#check @p2_eq_quarter
#print axioms p2_eq_quarter
#print axioms p2_feynman
