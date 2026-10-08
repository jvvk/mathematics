import AlmostSquares.Real
import AlmostSquares.Final
import AlmostSquares.Main
import AlmostSquares.Counts
import AlmostSquares.Reach
import AlmostSquares.Examples
import AlmostSquares.Parity
import AlmostSquares.Bouwkamp
import AlmostSquares.No16
import AlmostSquares.No17
import AlmostSquares.No19
import AlmostSquares.SearchFast
import AlmostSquares.Inflation
import AlmostSquares.Scales
import AlmostSquares.Classes

/-! Axiom audit. Everything depends only on `propext`, `Classical.choice` and `Quot.sound`, except the
    impossibility for n = 16, 17, 19, which uses `native_decide`: each use adds an auxiliary axiom
    asserting what the compiled search returned (trust in the compiler). Theorem 1 depends on them. -/

-- Theorem 1 for real rectangles, and for unit cells
#print axioms AlmostSq.almost_square_tilings_real
#print axioms AlmostSq.almost_square_tilings
#print axioms AlmostSq.friedman_twenty

-- Lemmas 2-4: balance, inflation, all large scales
#print axioms AlmostSq.balance
#print axioms AlmostSq.inflation
#print axioms AlmostSq.dissects_img
#print axioms AlmostSq.all_scales
#print axioms AlmostSq.inflOK_sound
#print axioms AlmostSq.inflCovers_sound

-- Lemma 5 and Proposition 6: parity
#print axioms AlmostSq.parity
#print axioms AlmostSq.parity_even
#print axioms AlmostSq.prop_112
#print axioms AlmostSq.prop_110
#print axioms AlmostSq.prop_139

-- The squared squares are the published Bouwkamp codes
#print axioms AlmostSq.sq112_code
#print axioms AlmostSq.sq110_code
#print axioms AlmostSq.sq139_code
#print axioms AlmostSq.moron_code

-- Corollary 7 and Lemma 8
#print axioms AlmostSq.shift_moments
#print axioms AlmostSq.signed_identity
#print axioms AlmostSq.integer_corners

-- Section 5: no tiling for the small n (n = 16, 17, 19 use native_decide)
#print axioms AlmostSq.noTilingF_sound
#print axioms AlmostSq.noTiling_16
#print axioms AlmostSq.noTiling_17
#print axioms AlmostSq.noTiling_19

-- Every printed number: Table 2, Section 4 counts, Figure 7, the 57 x 55 rectangle, Moron's rectangle
#print axioms AlmostSq.table2
#print axioms AlmostSq.uncovered_count
#print axioms AlmostSq.thresholds
#print axioms AlmostSq.residues
#print axioms AlmostSq.pieces
#print axioms AlmostSq.figure7
#print axioms AlmostSq.reach57_count
#print axioms AlmostSq.moron_60
#print axioms AlmostSq.moron_98
#print axioms AlmostSq.moron_admissible
