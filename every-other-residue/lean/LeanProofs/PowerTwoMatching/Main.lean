import LeanProofs.PowerTwoMatching.Basic

/-!
# Every other residue (MSE 2060312): axiom report

The matching with sums exactly the residues of parity `p` (`exists_matching`) and the impossibility
of the other parity (`parity_forced`), with the halving lemmas they use, and the remark that the
sums are never distinct modulo `2^k` (`not_distinct_mod`).
-/

#print axioms PowerTwoMatching.par_split
#print axioms PowerTwoMatching.mod_double
#print axioms PowerTwoMatching.mod_double_add_one
#print axioms PowerTwoMatching.exists_matching
#print axioms PowerTwoMatching.card_parity
#print axioms PowerTwoMatching.sum_parity
#print axioms PowerTwoMatching.parity_forced
#print axioms PowerTwoMatching.not_distinct_mod
