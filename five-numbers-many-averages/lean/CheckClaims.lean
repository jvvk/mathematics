import LeanProofs

open PairwiseAveraging
-- Lemma 1: dyadic weights; moves commute with affine maps and keep the sum
#check @weights
#print axioms weights
#check @affine
#print axioms affine
#check @sum_seq
#print axioms sum_seq
-- Lemma 2: no entry equals the mean before move k
#check @no_congruence
#print axioms no_congruence
#check @no_mean_before
#print axioms no_mean_before
-- Lemma 3: the count of entries at the mean
#check @count_step
#print axioms count_step
#check @count_ne_pred
#print axioms count_ne_pred
-- Theorem 1
#check @lower_bound
#print axioms lower_bound
#check @upper_bound
#print axioms upper_bound
#check @optimum
#print axioms optimum
#check @integer_version
#print axioms integer_version
#check @no_balanced_subset
#print axioms no_balanced_subset
