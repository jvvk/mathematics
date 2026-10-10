import LeanProofs.InversePairs.Limit

/-!
# Inverse pairs (MSE 5146740): axiom report

Weil's bound for Kloosterman sums is not in Mathlib; it enters every result below as the explicit
hypothesis `WeilBound p` (or `∀ p, WeilBound p`), never as an axiom. Lemma 1 (`rect`), Lemma 2
(`stair`), the divisor bound (`divisor_bound`), Lemma 3 (`R_le`), the full-grid limit (`C_close`),
the layer-cake identity (`key_identity`), the main inequality (`main_ineq`) and Theorem 1 (`rate`,
`tendsto_five`).
-/

#print axioms InversePairs.rect
#print axioms InversePairs.stair
#print axioms InversePairs.divisor_bound
#print axioms InversePairs.R_le
#print axioms InversePairs.C_close
#print axioms InversePairs.key_identity
#print axioms InversePairs.main_ineq
#print axioms InversePairs.rate
#print axioms InversePairs.tendsto_five
