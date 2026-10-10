import LeanProofs.LatinRank.Witness

/-!
# Latin squares of small rank: axiom report

Lemma 3 (`factor`), Theorem 1 (`rank_bound`, `rank_bound_strict`), Corollary 2 (`four_le_rank`,
`three_le_rank`) and the values `r(4) = 3`, `r(6) = 4`, `r(8) = 4` of "Latin squares of small rank".
`r(5) = 5` and `r(7) = 6` are certified by `../verify/certify_minrank.py`, not here.
-/

#print axioms LatinRank.factor
#print axioms LatinRank.rank_bound
#print axioms LatinRank.rank_bound_strict
#print axioms LatinRank.four_le_rank
#print axioms LatinRank.three_le_rank
#print axioms LatinRank.r4
#print axioms LatinRank.r6
#print axioms LatinRank.r8
