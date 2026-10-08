import LeanProofs

/-! Statements and axiom dependencies of every formalised claim of the paper
"Shuffle anti-squares of every even length from 24" (numbering of the October 2026 manuscript). -/

-- Theorem 2: U_k and W_k are shuffle anti-squares; Conjecture 1 holds.
#check @U_rotation_not_square
#check @W_isAntiSquare
#check @exists_antiSquare
-- Theorem 4: the blow-ups V(K, λ, μ), with K λ μ symbolic; and U_k = V(k + 9, 1, 1).
#check @Blocks.V_isAntiSquare
#check @Blocks.U_eq_V
-- Both conditions of Theorem 4 are needed.
#check @Blocks.V_8_1_1_not_anti
#check @Blocks.V_8_1_3_not_anti
#check @Blocks.V_9_1_2_not_anti
#check @Blocks.V_9_1_4_not_anti
-- Section 5: one cut only rotates; Corollary 6; the two-cut example for W_0.
#check @Blocks.cutsTo_one
#check @Blocks.antiSquare_needs_two_cuts
#check @Blocks.two_cuts_needed
#check @Blocks.W0_two_cut_example

#print axioms exists_antiSquare
#print axioms U_rotation_not_square
#print axioms Blocks.V_isAntiSquare
#print axioms Blocks.U_eq_V
#print axioms Blocks.V_8_1_1_not_anti
#print axioms Blocks.V_8_1_3_not_anti
#print axioms Blocks.V_9_1_2_not_anti
#print axioms Blocks.V_9_1_4_not_anti
#print axioms Blocks.two_cuts_needed
#print axioms Blocks.W0_two_cut_example
