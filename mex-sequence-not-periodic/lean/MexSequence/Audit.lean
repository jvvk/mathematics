import MexSequence.Main
import MexSequence.Twins

/-! Axiom audit: each result of the paper depends only on Lean's three standard axioms. -/

-- Lemma 1, Lemma 2 and Theorem 1 by the route of Section 4
#print axioms MexE27.zeros
#print axioms MexE27.twins
#print axioms MexE27.unbounded_of_twins
#print axioms MexE27.not_eventually_periodic_of_twins
-- Lemma 3 and Theorem 2 (the closed form `F` is the sequence), and Theorem 1 again from them
#print axioms MexE27.isMex_F
#print axioms MexE27.eq_F
#print axioms MexE27.unbounded
#print axioms MexE27.not_eventually_periodic
