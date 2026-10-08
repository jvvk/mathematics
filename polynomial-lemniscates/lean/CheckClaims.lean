import LeanProofs
-- Theorem 1
#check @Lemniscates.theoremA
#print axioms Lemniscates.theoremA
-- Corollary 2 and the six points of Figure 1
#check @Lemniscates.oval_le_six
#print axioms Lemniscates.oval_le_six
#check @Lemniscates.bernoulli_six
#print axioms Lemniscates.bernoulli_six
-- Corollary 3, second part
#check @Lemniscates.M_eq_iff
#print axioms Lemniscates.M_eq_iff
-- Lemma 4 (pairing), Lemma 5 (trace formula)
#check @Lemniscates.real_card_le
#print axioms Lemniscates.real_card_le
#check @Lemniscates.TraceFormula.trace_eq
#print axioms Lemniscates.TraceFormula.trace_eq
#check @Lemniscates.TraceFormula.mem_S_of_algHom
#print axioms Lemniscates.TraceFormula.mem_S_of_algHom
-- Lemma 6 (no common factor)
#check @Lemniscates.no_common_prime
#print axioms Lemniscates.no_common_prime
#check @Lemniscates.no_common_prime_zero
#print axioms Lemniscates.no_common_prime_zero
-- Lemma 7 (resultant top and next coefficients)
#check @Lemniscates.ResTop.resultant_top
#print axioms Lemniscates.ResTop.resultant_top
#check @Lemniscates.ResTop.resultant_subtop
#print axioms Lemniscates.ResTop.resultant_subtop
-- Proposition 8 (deformation)
#check @Lemniscates.Integral.exists_monic
#print axioms Lemniscates.Integral.exists_monic
#check @Lemniscates.Fibre.trace_fibre
#print axioms Lemniscates.Fibre.trace_fibre
#check @Lemniscates.Deform.fibre_multiset
#print axioms Lemniscates.Deform.fibre_multiset
-- Lemma 9 (growth) and constancy
#check @Lemniscates.GrowthGen.growth_level
#print axioms Lemniscates.GrowthGen.growth_level
#check @Lemniscates.GrowthGen.growth_zero
#print axioms Lemniscates.GrowthGen.growth_zero
#check @Lemniscates.Deform.tau_const
#print axioms Lemniscates.Deform.tau_const
-- Lemma 10 (level zero), Proposition 11 (trace identity), Theorem 1 coprime case
#check @Lemniscates.Level0.level0
#print axioms Lemniscates.Level0.level0
#check @Lemniscates.CaseI.trace_identity
#print axioms Lemniscates.CaseI.trace_identity
#check @Lemniscates.CaseI.caseI
#print axioms Lemniscates.CaseI.caseI
-- Lemmas 12, 13 and the shared-root case
#check @Lemniscates.CaseII.R_natDegree_le
#print axioms Lemniscates.CaseII.R_natDegree_le
#check @Lemniscates.CaseII.count_of_R_ne_zero
#print axioms Lemniscates.CaseII.count_of_R_ne_zero
#check @Lemniscates.CaseII.pow_eq
#print axioms Lemniscates.CaseII.pow_eq
#check @Lemniscates.CaseII.empty_of_R_eq_zero
#print axioms Lemniscates.CaseII.empty_of_R_eq_zero
