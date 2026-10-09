import LeanProofs

-- Definitions: agreement through triples is the same as `S|Y ≅ T|Y`
#check @BalancedMast.Tree.agree_iff_restrict_iso
#print axioms BalancedMast.Tree.agree_iff_restrict_iso
#print axioms BalancedMast.Tree.iso_of_triples
-- Lemma 3.1 (substitution), Corollary 3.2, Theorem 1.1(1)
#check @BalancedMast.Tree.mast_bind_le
#print axioms BalancedMast.Tree.mast_bind_le
#check @BalancedMast.M_add_le
#print axioms BalancedMast.M_add_le
#check @BalancedMast.tendsto_beta
#print axioms BalancedMast.tendsto_beta
-- Bordewich et al., Lemma 4.5; the k = 3 pair; Theorem 1.1(2)
#check @BalancedMast.Tree.mast_le_of_cellsSmall
#print axioms BalancedMast.Tree.mast_le_of_cellsSmall
#check @BalancedMast.M_eleven
#print axioms BalancedMast.M_eleven
#check @BalancedMast.M_upper
#print axioms BalancedMast.M_upper
#check @BalancedMast.beta_le_five_elevenths
#print axioms BalancedMast.beta_le_five_elevenths
-- Section 5: the one-level induction, Lemma 5.1 (checked certificate), M(n) ≥ n^0.235
#check @BalancedMast.ansatz_one
#print axioms BalancedMast.ansatz_one
#check @BalancedMast.certOne
#print axioms BalancedMast.certOne
#check @BalancedMast.M_lower_235
#print axioms BalancedMast.M_lower_235
-- Section 5: the two-level induction; Theorem 1.1(3) from the inequality of Lemma 5.3 (a hypothesis)
#check @BalancedMast.CertTwo
#check @BalancedMast.ansatz_two
#print axioms BalancedMast.ansatz_two
#check @BalancedMast.M_lower
#print axioms BalancedMast.M_lower
