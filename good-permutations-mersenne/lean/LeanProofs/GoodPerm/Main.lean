import LeanProofs.GoodPerm.Construction
import LeanProofs.GoodPerm.Mersenne

/-!
# Good permutations (MO 514690): axiom report

Theorem 1 (Bîsceanu: only lengths `2^m - 1`, via `two_adic`, `congr_shift`, `pair_gap`,
`middle_sum`), the search reduction, and Theorem 2 (the asker's permutation: `block_dvd_iff`,
`good_iff_prime`, `c_perm`). The exhaustive searches for `n = 15, 31, 63` are in Python/C, not Lean.
-/

#print axioms GoodPerm.two_adic
#print axioms GoodPerm.congr_shift
#print axioms GoodPerm.pair_gap
#print axioms GoodPerm.middle_sum
#print axioms GoodPerm.mersenne
#print axioms GoodPerm.reduction
#print axioms GoodPerm.c_perm
#print axioms GoodPerm.block_dvd_iff
#print axioms GoodPerm.good_iff_prime
