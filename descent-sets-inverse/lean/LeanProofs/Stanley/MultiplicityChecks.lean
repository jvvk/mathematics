/- Kernel checks distinguishing joint descent counts from single-descent counts. -/
import LeanProofs.Stanley.JointMultiplicity

namespace Stanley

/-- The empty permutation has the empty joint descent pair. -/
theorem beta_zero_empty : beta 0 ∅ ∅ = 1 := by decide

/-- Two alternating permutations of length four have both descent sets prescribed. -/
theorem beta_four_alternating : beta 4 {0, 2} {0, 2} = 2 := by decide

/-- This mixed entry is nonzero, but smaller than the corresponding diagonal entry. -/
theorem beta_four_mixed : beta 4 {0} {1} = 1 := by decide

theorem beta_four_middle : beta 4 {1} {1} = 2 := by decide

/-- The diagonal inequality is genuinely an inequality, not a general equality. -/
theorem beta_four_strict :
    beta 4 {0} {1} ^ 2 < beta 4 {0} {0} * beta 4 {1} {1} := by decide

end Stanley
