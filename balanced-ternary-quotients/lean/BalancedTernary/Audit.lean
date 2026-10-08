import BalancedTernary.BT
import BalancedTernary.Fam_10_m11_4r2
import BalancedTernary.Fam_10_m19_4r2
import BalancedTernary.Fam_16_p17_2r0
import BalancedTernary.Fam_20_m19_4r2
import BalancedTernary.Fam_40_p41_4r0
import BalancedTernary.Fam_4_m5
import BalancedTernary.Fam_4_p5
import BalancedTernary.Fam_5_m4_4r2
import BalancedTernary.Fam_5_p4_4r0
import BalancedTernary.Fam_8_m17_2r0
import BalancedTernary.Fam_8_m7
import BalancedTernary.Fam_8_p17
import BalancedTernary.Fam_8_p7

/-! Axiom audit: every theorem of the paper depends only on Lean's standard axioms. -/

-- Section 3 by hand: 4*3^k + 5 for k >= 5, and the corollary
#print axioms four_pow_plus_five_not_in_BB
#print axioms infinitely_many_exceptions
-- Theorem 1.1
#print axioms Tern.not_BB_4_p5
#print axioms Tern.not_BB_4_m5
#print axioms Tern.not_BB_8_p7
#print axioms Tern.not_BB_8_p17
#print axioms Tern.not_BB_8_m7
-- Theorem 1.3
#print axioms Tern.not_BB_8_m17_2r0
#print axioms Tern.not_BB_16_p17_2r0
#print axioms Tern.not_BB_10_m11_4r2
#print axioms Tern.not_BB_10_m19_4r2
#print axioms Tern.not_BB_20_m19_4r2
#print axioms Tern.not_BB_5_m4_4r2
#print axioms Tern.not_BB_5_p4_4r0
#print axioms Tern.not_BB_40_p41_4r0
