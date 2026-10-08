/-
  **Theorem 1** of the paper, in full: for `n ≥ 1`, the rectangle `R_n` (width `n + 1`, height `n`)
  has an admissible tiling (distinct almost-squares `k × (k+1)`, `1 ≤ k < n`, covering every unit
  cell exactly once) if and only if `n ∈ {4, 10, 12, 14, 15, 18}` or `n ≥ 20`.

  To review, read `Tile`, `Tile.size`, `Tile.cells`, `rect` and `Admissible` in `Basic.lean` and
  the statement below; everything else is checked by Lean's kernel.
-/
import AlmostSquares.Main
import AlmostSquares.NoSmall
import AlmostSquares.No16
import AlmostSquares.No17
import AlmostSquares.No19

namespace AlmostSq

theorem almost_square_tilings (n : ℕ) (hn : 1 ≤ n) :
    (∃ ts : List Tile, Admissible n ts) ↔ n ∈ [4, 10, 12, 14, 15, 18] ∨ 20 ≤ n := by
  constructor
  · rintro ⟨ts, hA⟩
    by_contra hc
    have hlt : n < 20 := by
      by_contra h
      exact hc (Or.inr (by omega))
    have hmem : n ∈ [1, 2, 3, 5, 6, 7, 8, 9, 11, 13] ∨ n = 16 ∨ n = 17 ∨ n = 19 := by
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hc ⊢
      omega
    have hno : noTilingF n = true := by
      rcases hmem with h | rfl | rfl | rfl
      · exact noTiling_small n h
      · exact noTiling_16
      · exact noTiling_17
      · exact noTiling_19
    exact noTilingF_sound (by omega) hno ts hA
  · exact friedman_twenty n

end AlmostSq
