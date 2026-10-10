import LeanProofs

open PrimeSquares
-- a nonzero nonunit dividing a product of two primes is divisible by one of them
#check @prime_dvd_of_dvd_mul
#print axioms prime_dvd_of_dvd_mul
-- the orientation argument (Theorems 1 and 2, odd p): q₁ ∣ F or q₂ ∣ F
#check @orientation_dichotomy
#print axioms orientation_dichotomy
-- Q_p irreducible over ℤ, and Q_p(1) = p
#check @cyclotomic_prime_irreducible
#print axioms cyclotomic_prime_irreducible
#check @cyclotomic_prime_eval_one
#print axioms cyclotomic_prime_eval_one
-- Lemma 1: one row, then the whole tile is a bar
#check @row_eq
#print axioms row_eq
#check @bar_of_dvd
#print axioms bar_of_dvd
