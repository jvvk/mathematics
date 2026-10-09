import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic

/-!
# Unit hexagons: angle counting (Sections 4 and 5, and the octagon reduction)

With diameter at most `√2`, every convex interior angle lies in `(0, π/2]` and every reflex one in
`[3π/2, 2π)`. Angle sums then give:
* (Lemma 4.2) a pocket with `k` intermediate vertices, `k - r` of them convex in the polygon, has
  `3 (k - r) < 2k`, that is `r > k/3`;
* an `n`-gon has `r` reflex vertices with `n - 4 ≤ 3r < 2(n - 2)`: so `r ∈ {1, 2}` for `n = 6` and
  `r ∈ {2, 3}` for `n = 8`;
* (Theorem 1, two reflex vertices) the four convex angles sum to `β₁ + β₂ ≤ π`, so two disjoint convex
  pairs, each with sum `> π/2` by Lemma 2.1, are impossible;
* (Proposition 6.1) the contact count for an octagon with two pockets.
-/

open Real Finset

namespace UnitHexagon

/-- Lemma 4.2 (reflex cost): pocket angles `φ` at the `k` intermediate vertices and `e₁, e₂` at the
ends, all positive, sum to `kπ`; those at the convex vertices `C` are at least `3π/2`. -/
theorem pocket_cost {k : ℕ} (φ : Fin k → ℝ) {e₁ e₂ : ℝ} (C : Finset (Fin k))
    (hpos : ∀ i, 0 < φ i) (he₁ : 0 < e₁) (he₂ : 0 < e₂) (hsum : ∑ i, φ i + e₁ + e₂ = k * π)
    (hC : ∀ i ∈ C, 3 * π / 2 ≤ φ i) : 3 * C.card < 2 * k := by
  have h1 : ∑ i ∈ C, φ i ≤ ∑ i, φ i :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ C) (fun i _ _ => (hpos i).le)
  have h2 : (C.card : ℝ) * (3 * π / 2) ≤ ∑ i ∈ C, φ i := by
    have := Finset.card_nsmul_le_sum C φ (3 * π / 2) hC
    simpa [nsmul_eq_mul] using this
  have h3 : (C.card : ℝ) * (3 * π / 2) < k * π := by linarith
  have h4 : (3 * C.card : ℝ) < 2 * k := by nlinarith [Real.pi_pos]
  exact_mod_cast h4

/-- Reflex counts of an `n`-gon of diameter at most `√2`. -/
theorem reflex_count {n : ℕ} (ι : Fin n → ℝ) (R : Finset (Fin n))
    (hconv : ∀ i ∉ R, 0 < ι i ∧ ι i ≤ π / 2) (hrefl : ∀ i ∈ R, 3 * π / 2 ≤ ι i ∧ ι i < 2 * π)
    (hsum : ∑ i, ι i = (n - 2 : ℝ) * π) :
    (n : ℝ) - 4 ≤ 3 * R.card ∧ 3 * (R.card : ℝ) < 2 * (n - 2) := by
  have split := Finset.sum_add_sum_compl R ι
  have up1 : ∑ i ∈ R, ι i ≤ R.card * (2 * π) := by
    have := Finset.sum_le_card_nsmul R ι (2 * π) (fun i hi => (hrefl i hi).2.le)
    simpa [nsmul_eq_mul] using this
  have up2 : ∑ i ∈ Rᶜ, ι i ≤ Rᶜ.card * (π / 2) := by
    have := Finset.sum_le_card_nsmul Rᶜ ι (π / 2) (fun i hi => (hconv i (Finset.mem_compl.1 hi)).2)
    simpa [nsmul_eq_mul] using this
  have lo1 : (R.card : ℝ) * (3 * π / 2) ≤ ∑ i ∈ R, ι i := by
    have := Finset.card_nsmul_le_sum R ι (3 * π / 2) (fun i hi => (hrefl i hi).1)
    simpa [nsmul_eq_mul] using this
  have hcard : (Rᶜ.card : ℝ) = n - R.card := by
    rw [Finset.card_compl, Fintype.card_fin, Nat.cast_sub (Finset.card_le_univ R |>.trans_eq (by simp))]
  -- the complement is nonempty: n reflex angles would already exceed the total
  have hne : Rᶜ.Nonempty := by
    by_contra hc
    rw [Finset.not_nonempty_iff_eq_empty, Finset.compl_eq_empty_iff] at hc
    have : (R.card : ℝ) = n := by rw [hc, Finset.card_univ, Fintype.card_fin]
    have h0 : ∑ i ∈ Rᶜ, ι i = 0 := by rw [hc, Finset.compl_univ, Finset.sum_empty]
    nlinarith [Real.pi_pos]
  have lo2 : 0 < ∑ i ∈ Rᶜ, ι i :=
    Finset.sum_pos (fun i hi => (hconv i (Finset.mem_compl.1 hi)).1) hne
  constructor
  · nlinarith [Real.pi_pos]
  · nlinarith [Real.pi_pos]

theorem hexagon_reflex_count (ι : Fin 6 → ℝ) (R : Finset (Fin 6))
    (hconv : ∀ i ∉ R, 0 < ι i ∧ ι i ≤ π / 2) (hrefl : ∀ i ∈ R, 3 * π / 2 ≤ ι i ∧ ι i < 2 * π)
    (hsum : ∑ i, ι i = 4 * π) : R.card = 1 ∨ R.card = 2 := by
  have := reflex_count ι R hconv hrefl (by rw [hsum]; norm_num)
  obtain ⟨h1, h2⟩ := this
  norm_num at h1 h2
  have a : 2 ≤ 3 * R.card := by exact_mod_cast (by linarith : (2 : ℝ) ≤ 3 * R.card)
  have b : 3 * R.card < 8 := by exact_mod_cast (by linarith : (3 * R.card : ℝ) < 8)
  omega

theorem octagon_reflex_count (ι : Fin 8 → ℝ) (R : Finset (Fin 8))
    (hconv : ∀ i ∉ R, 0 < ι i ∧ ι i ≤ π / 2) (hrefl : ∀ i ∈ R, 3 * π / 2 ≤ ι i ∧ ι i < 2 * π)
    (hsum : ∑ i, ι i = 6 * π) : R.card = 2 ∨ R.card = 3 := by
  have := reflex_count ι R hconv hrefl (by rw [hsum]; norm_num)
  obtain ⟨h1, h2⟩ := this
  norm_num at h1 h2
  have a : 4 ≤ 3 * R.card := by exact_mod_cast (by linarith : (4 : ℝ) ≤ 3 * R.card)
  have b : 3 * R.card < 12 := by exact_mod_cast (by linarith : (3 * R.card : ℝ) < 12)
  omega

/-- Two reflex vertices with smaller angles `β₁, β₂ ≤ π/2`: the four convex angles sum to `β₁ + β₂`,
which cannot hold two disjoint adjacent convex pairs, each with sum `> π/2`. -/
theorem two_disjoint_pairs_impossible {θ₁ θ₂ θ₃ θ₄ β₁ β₂ : ℝ}
    (hsum : θ₁ + θ₂ + θ₃ + θ₄ + (2 * π - β₁) + (2 * π - β₂) = 4 * π)
    (hb₁ : β₁ ≤ π / 2) (hb₂ : β₂ ≤ π / 2) (p₁ : π / 2 < θ₁ + θ₂) (p₂ : π / 2 < θ₃ + θ₄) : False := by
  linarith

/-- Proposition 6.1, two pockets: each holds one reflex vertex, so `k < 3` and `k ≠ 2`, hence `k = 1`;
then `m = 6` hull contacts, against `m ≤ q + 3 = 5`. -/
theorem octagon_two_pockets {m k₁ k₂ : ℕ} (hsum : m + k₁ + k₂ = 8) (hk₁ : 1 ≤ k₁) (hk₂ : 1 ≤ k₂)
    (hc₁ : k₁ < 3) (hc₂ : k₂ < 3) (h2₁ : k₁ ≠ 2) (h2₂ : k₂ ≠ 2) (hm : m ≤ 2 + 3) : False := by
  omega

end UnitHexagon
