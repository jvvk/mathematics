import AlternatingSum.Series

/-!
  Theorem 1 of the paper: for `n ≤ a + b` and `ν = a + b - n`,
  `L(u,a,b,n) = (u+ν)!² / ν! · [w^a z^b] R^(u+1) (R-1)^ν`,  `R = 1/((1-z)² - w²)`.
-/

namespace Abdesselam

open MvPowerSeries Finset Nat

/-- Regrouping the double sum over `k, ℓ` by `s = k + ℓ`: the terms with `s < k` or
`s > k + b` vanish because `C(s,k) = 0` or `C(a+b-s, a-k) = 0`. -/
theorem regroup (a b : ℕ) (f : ℕ → ℚ) :
    ∑ k ∈ range (a + 1), ∑ l ∈ range (b + 1),
        (-1) ^ k * ((k + l).choose k : ℚ) * ((a + b - (k + l)).choose (a - k) : ℚ) * f (k + l) =
      ∑ s ∈ range (a + b + 1), f s * P s (a + b - s) a := by
  simp_rw [P, mul_sum]
  conv_rhs => rw [sum_comm]
  refine sum_congr rfl fun k hk ↦ ?_
  have hk := mem_range.1 hk
  have hsub : (range (b + 1)).map (addLeftEmbedding k) ⊆ range (a + b + 1) := by
    intro s hs
    simp only [mem_map, mem_range, addLeftEmbedding_apply] at hs ⊢
    omega
  rw [← sum_subset hsub, sum_map]
  · refine sum_congr rfl fun l _ ↦ ?_
    simp only [addLeftEmbedding_apply]
    ring
  · intro s hs hs'
    simp only [mem_map, mem_range, addLeftEmbedding_apply, not_exists, not_and] at hs hs'
    rcases Nat.lt_or_ge s k with h | h
    · rw [Nat.choose_eq_zero_of_lt h]; simp
    · have : a + b - s < a - k := by
        by_contra hc; exact hs' (s - k) (by omega) (by omega)
      rw [Nat.choose_eq_zero_of_lt this]; simp

/-- **Theorem 1.** -/
theorem main (u a b n : ℕ) (hn : n ≤ a + b) :
    L u a b n = ((u + (a + b - n)) ! : ℚ) ^ 2 / ((a + b - n) ! : ℚ) *
      coeff (mono a b) (R ^ (u + 1) * (R - 1) ^ (a + b - n)) := by
  rw [step1 u a b n hn, ← subst_H, coeff_subst_ab]
  simp_rw [coeff_H, mono_zero, mono_one]
  simp_rw [Nat.sub_sub]
  rw [show u + (a + b - n) = u + a + b - n by omega,
    regroup a b (fun s ↦ c u (a + b - n) s (a + b - s))]

end Abdesselam
