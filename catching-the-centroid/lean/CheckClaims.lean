import LeanProofs

open CentroidCircle
-- Proposition 1 (key identity) and its corollary for centrally symmetric regions
#check @key
#print axioms key
#print axioms symmetric_half
-- formula (3): the signed-area form
#check @signed_area
#print axioms signed_area
-- equation (4) and Proposition 2 (the product bound)
#print axioms integral_abs_ρo
#check @product_bound
#print axioms product_bound
-- Grünbaum's inequality in angular form, and Theorem 1 (with Stewart's inequality as input)
#print axioms abs_b_le
#check @abs_P_sub_half_le
#print axioms abs_P_sub_half_le
#check @P_le_14_27
#print axioms P_le_14_27
-- Levi's 2/5 via Minkowski-Radon, and the weaker bound 8/15 of Section 4
#print axioms one_sub_s_le
#check @P_le_8_15
#print axioms P_le_8_15
-- Lemma 1 (three lines), Proposition 3, and 14/27 for three-sided regions from Grünbaum alone
#check @three_sectors
#print axioms three_sectors
#print axioms s_ge_two_thirds
#check @P_le_14_27_three_sided
#print axioms P_le_14_27_three_sided
-- the hypotheses are satisfiable
#print axioms uniform_dens
