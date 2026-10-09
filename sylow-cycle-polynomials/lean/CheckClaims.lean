import LeanProofs

open Polynomial StanleySylow

-- Lemma 1: the norm computation and the quadratic composition criterion
#check @StanleySylow.monic_comp_quad
#print axioms StanleySylow.norm_sub_eval
#print axioms StanleySylow.monic_comp_quad
-- Theorem 1 (the Sylow polynomials P_n, recurrence P_{n+1} = P_n (P_n + |G|)):
-- factorization, degrees, coefficient agreement, irreducibility over Q, for every n
#check StanleySylow.sylow_factorization
#print axioms StanleySylow.sylow_factorization
#check StanleySylow.sylow_factors_degree
#check StanleySylow.sylow_top_coeffs_agree
#print axioms StanleySylow.sylow_top_coeffs_agree
#check StanleySylow.sylow_irreducible_mod5
#check StanleySylow.sylow_irreducible_rat
#print axioms StanleySylow.sylow_irreducible_rat
-- Corollary (the polynomials as printed in MO 489315, question's indexing)
#check StanleySylow.stanleyF_recurrence
#check StanleySylow.stanley_factorization
#print axioms StanleySylow.stanley_factorization
#check StanleySylow.top_coeffs_agree
#print axioms StanleySylow.top_coeffs_agree
#check StanleySylow.stanley_irreducible_rat
#print axioms StanleySylow.stanley_irreducible_rat

-- the question's example
example : stanleyA 3 = X^4 + C 2 * X^3 - X + C 2 := by
  simp [stanleyA, stanleyF, stanley_a, f, a, quad]
  ring
