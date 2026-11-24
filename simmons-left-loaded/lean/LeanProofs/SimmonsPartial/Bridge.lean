import LeanProofs.SimmonsPartial.Basic

/-!
# Bridge to the probabilities

For `p = m / n` and `0 < n`, `m ≤ n`, the binomial mass `C(n, j) p^j (1 - p)^(n - j)` equals
`w n m j / n ^ n`, so `α_i = P(X ≤ m - i) - P(X ≥ m + i) = A n m i / n ^ n`.
-/

namespace SimmonsPartial

open Finset

lemma pmf_eq {n m j : ℕ} (hmn : m ≤ n) (hn : 0 < n) (hj : j ≤ n) :
    (n.choose j : ℝ) * ((m : ℝ) / n) ^ j * (1 - (m : ℝ) / n) ^ (n - j) = (w n m j : ℝ) / (n : ℝ) ^ n := by
  have hn' : (n : ℝ) ≠ 0 := by positivity
  have h1 : 1 - (m : ℝ) / n = ((n - m : ℕ) : ℝ) / n := by rw [Nat.cast_sub hmn]; field_simp
  rw [h1, div_pow, div_pow, w]
  push_cast
  rw [show (n : ℝ) ^ n = n ^ j * n ^ (n - j) by rw [← pow_add, Nat.add_sub_cancel' hj]]
  field_simp

/-- **Bridge.** `P(X ≤ m - i) - P(X ≥ m + i) = A n m i / n ^ n` for `X ~ Bin(n, m/n)`. -/
theorem alpha_eq (n m i : ℕ) (hmn : m ≤ n) (hn : 0 < n) :
    (∑ j ∈ (range (n + 1)).filter (fun j => j + i ≤ m),
        (n.choose j : ℝ) * ((m : ℝ) / n) ^ j * (1 - (m : ℝ) / n) ^ (n - j)) -
      (∑ j ∈ (range (n + 1)).filter (fun j => m + i ≤ j),
        (n.choose j : ℝ) * ((m : ℝ) / n) ^ j * (1 - (m : ℝ) / n) ^ (n - j)) =
      (A n m i : ℝ) / (n : ℝ) ^ n := by
  have hc : ∀ s : Finset ℕ, s ⊆ range (n + 1) →
      ∑ j ∈ s, (n.choose j : ℝ) * ((m : ℝ) / n) ^ j * (1 - (m : ℝ) / n) ^ (n - j) =
        (∑ j ∈ s, (w n m j : ℝ)) / (n : ℝ) ^ n := fun s hs => by
    rw [sum_div]
    exact sum_congr rfl fun j hj => pmf_eq hmn hn (by have := hs hj; simp only [mem_range] at this; omega)
  rw [hc _ (filter_subset _ _), hc _ (filter_subset _ _), ← sub_div, A]
  push_cast
  rfl

end SimmonsPartial
