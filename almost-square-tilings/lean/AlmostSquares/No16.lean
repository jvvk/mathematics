/- Impossibility for `n = 16`: the search of SearchFast.lean, proved sound there, evaluated by
   compiled code (`native_decide`, which adds an auxiliary axiom asserting the compiled result). The kernel run needs
   more memory than a laptop has; the cases `n ≤ 13` in NoSmall.lean are checked by the kernel. -/
import AlmostSquares.SearchFast

namespace AlmostSq

theorem noTiling_16 : noTilingF 16 = true := by native_decide

end AlmostSq
