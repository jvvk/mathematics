import LeanProofs.BalancedMast.Restrict
import LeanProofs.BalancedMast.Example
import LeanProofs.BalancedMast.CertOne
import LeanProofs.BalancedMast.TwoLevel

/-! # Agreement subtrees of balanced trees: headline results -/

-- Definitions: triple-based agreement is `S|Y ≅ T|Y`
#print axioms BalancedMast.Tree.iso_of_triples
#print axioms BalancedMast.Tree.agree_iff_restrict_iso
-- Lemma 3.1 (substitution), Corollary 3.2, Theorem 1.1(1)
#print axioms BalancedMast.Tree.mast_bind_le
#print axioms BalancedMast.M_add_le
#print axioms BalancedMast.tendsto_beta
-- Bordewich et al. Lemma 4.5 and the k = 3 example; Theorem 1.1(2)
#print axioms BalancedMast.Tree.mast_le_of_cellsSmall
#print axioms BalancedMast.M_eleven
#print axioms BalancedMast.M_upper
#print axioms BalancedMast.beta_le_five_elevenths
-- Section 5: one-level induction, Lemma 5.1 checked, M(n) ≥ n^0.235
#print axioms BalancedMast.ansatz_one
#print axioms BalancedMast.certOne
#print axioms BalancedMast.M_lower_235
-- Section 5: two-level induction; Theorem 1.1(3) from the inequality of Lemma 5.3
#print axioms BalancedMast.ansatz_two
#print axioms BalancedMast.M_lower
