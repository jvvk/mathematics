/- Kernel-checked impossibility for the small `n ≤ 13` without an admissible tiling. -/
import AlmostSquares.SearchFast

namespace AlmostSq

theorem noTiling_small : ∀ n ∈ [1, 2, 3, 5, 6, 7, 8, 9, 11, 13], noTilingF n = true := by
  decide +kernel

end AlmostSq
