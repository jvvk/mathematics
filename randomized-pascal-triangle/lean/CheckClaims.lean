import LeanProofs

-- Theorem 1: E S_n ≥ λ(p)^n, and λ(p) > 1 exactly when 2p² - 4p + 1 < 0
#check RandPascal.theoremA
#print axioms RandPascal.theoremA
#check RandPascal.one_lt_lamA
#print axioms RandPascal.one_lt_lamA
-- Corollary: L_p = ∞ for p > 1 - 1/√2
#check RandPascal.meanN_diverges_A
#print axioms RandPascal.meanN_diverges_A
-- Theorem 2, from the local inequality (certified outside Lean)
#check RandPascal.theoremB
#print axioms RandPascal.theoremB
#check RandPascal.theoremB_quarter
#print axioms RandPascal.theoremB_quarter
#check RandPascal.meanN_diverges_B
#print axioms RandPascal.meanN_diverges_B
-- the local inequality in Lean is the function the certificate checks
#check RandPascal.bridge1
#check RandPascal.bridge5
