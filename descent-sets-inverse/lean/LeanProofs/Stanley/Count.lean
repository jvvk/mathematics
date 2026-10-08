/-
  Part E. Permutations of `Fin n`, the count `f n`, and its bounds.

  `f n` is the number of pairs `(D σ, D σ⁻¹)` over all permutations `σ` of `Fin n`, where `D` is the
  (0-indexed) descent set. Every pair of equal-size subsets of `{0, …, n-2}` occurs, so
  `C(2n-2, n-1) ≤ f n ≤ 4^(n-1)`.
-/
import LeanProofs.Stanley.Pivot
import Mathlib.Data.Nat.Choose.Vandermonde
import Mathlib.Data.Nat.Choose.Central
import Mathlib.Data.Fintype.Perm

namespace Stanley

open Finset

/-- Descent set of a permutation of `Fin n`, as a subset of `{0, …, n-2}`. -/
def descP {n : ℕ} (σ : Equiv.Perm (Fin n)) : Finset ℕ :=
  (range (n - 1)).filter (fun i => ∃ h : i + 1 < n, σ ⟨i + 1, h⟩ < σ ⟨i, by omega⟩)

/-- All pairs (descent set, inverse descent set). -/
def pairs (n : ℕ) : Finset (Finset ℕ × Finset ℕ) :=
  (Finset.univ : Finset (Equiv.Perm (Fin n))).image (fun σ => (descP σ, descP σ⁻¹))

/-- Stanley's `f(n)`. -/
def f (n : ℕ) : ℕ := (pairs n).card

/-- A bijection of `{0, …, n-1}` given by `ℕ`-functions, as a permutation of `Fin n`. -/
def toPerm {n : ℕ} (w u : ℕ → ℕ) (hw : ∀ q < n, w q < n) (hu : ∀ x < n, u x < n)
    (huw : ∀ q < n, u (w q) = q) (hwu : ∀ x < n, w (u x) = x) : Equiv.Perm (Fin n) where
  toFun i := ⟨w i, hw i i.2⟩
  invFun x := ⟨u x, hu x x.2⟩
  left_inv i := Fin.ext (huw i i.2)
  right_inv x := Fin.ext (hwu x x.2)

theorem descP_toPerm {n : ℕ} {w u : ℕ → ℕ} (hw : ∀ q < n, w q < n) (hu : ∀ x < n, u x < n)
    (huw : ∀ q < n, u (w q) = q) (hwu : ∀ x < n, w (u x) = x) :
    descP (toPerm w u hw hu huw hwu) = desc n w ∧ descP (toPerm w u hw hu huw hwu)⁻¹ = desc n u := by
  constructor
  · ext i
    simp only [descP, desc, Finset.mem_filter, Finset.mem_range]
    constructor
    · rintro ⟨hi, h, hlt⟩; exact ⟨hi, hlt⟩
    · rintro ⟨hi, hlt⟩; exact ⟨hi, by omega, hlt⟩
  · ext i
    simp only [descP, desc, Finset.mem_filter, Finset.mem_range]
    constructor
    · rintro ⟨hi, h, hlt⟩; exact ⟨hi, hlt⟩
    · rintro ⟨hi, hlt⟩; exact ⟨hi, by omega, hlt⟩

/-- **Every pair of equal-size descent sets occurs.** -/
theorem mem_pairs {n : ℕ} {S T : Finset ℕ} (hS : S ⊆ range (n - 1)) (hT : T ⊆ range (n - 1))
    (hk : S.card = T.card) : (S, T) ∈ pairs n := by
  obtain ⟨w, u, hw, hu, huw, hwu, hdw, hdu⟩ := exists_pair hS hT hk
  obtain ⟨h1, h2⟩ := descP_toPerm hw hu huw hwu
  exact Finset.mem_image.mpr ⟨toPerm w u hw hu huw hwu, Finset.mem_univ _, by rw [h1, h2, hdw, hdu]⟩

/-- Pairs of equal-size subsets of `{0, …, n-2}`. -/
def eqPairs (n : ℕ) : Finset (Finset ℕ × Finset ℕ) :=
  ((range (n - 1)).powerset ×ˢ (range (n - 1)).powerset).filter (fun st => st.1.card = st.2.card)

theorem card_eqPairs (n : ℕ) : (eqPairs n).card = (2 * (n - 1)).choose (n - 1) := by
  rw [← Nat.sum_range_choose_sq]
  unfold eqPairs
  rw [Finset.card_filter, Finset.sum_product]
  have inner : ∀ S ∈ (range (n - 1)).powerset,
      (∑ T ∈ (range (n - 1)).powerset, if S.card = T.card then 1 else 0) = (n - 1).choose S.card := by
    intro S _
    rw [← Finset.card_filter]
    have : (range (n - 1)).powerset.filter (fun T => S.card = T.card) =
        (range (n - 1)).powersetCard S.card := by
      rw [Finset.powersetCard_eq_filter]
      ext T; simp only [Finset.mem_filter]; constructor <;> rintro ⟨h1, h2⟩ <;> exact ⟨h1, h2.symm⟩
    rw [this, Finset.card_powersetCard, Finset.card_range]
  rw [Finset.sum_congr rfl inner]
  have := Finset.sum_powerset_apply_card (f := fun m => (n - 1).choose m) (x := range (n - 1))
  rw [this, Finset.card_range]
  apply Finset.sum_congr rfl
  intro m _
  rw [smul_eq_mul, sq]

theorem eqPairs_subset (n : ℕ) : eqPairs n ⊆ pairs n := by
  intro st hst
  simp only [eqPairs, Finset.mem_filter, Finset.mem_product, Finset.mem_powerset] at hst
  exact mem_pairs hst.1.1 hst.1.2 hst.2

/-- **Lower bound.** `f n ≥ C(2n-2, n-1)`. -/
theorem choose_le_f (n : ℕ) : (2 * (n - 1)).choose (n - 1) ≤ f n := by
  rw [← card_eqPairs]; exact Finset.card_le_card (eqPairs_subset n)

/-- **Upper bound.** `f n ≤ 4^(n-1)`. -/
theorem f_le (n : ℕ) : f n ≤ 4 ^ (n - 1) := by
  have hsub : pairs n ⊆ (range (n - 1)).powerset ×ˢ (range (n - 1)).powerset := by
    intro st hst
    obtain ⟨σ, _, rfl⟩ := Finset.mem_image.mp hst
    simp only [Finset.mem_product, Finset.mem_powerset]
    exact ⟨Finset.filter_subset _ _, Finset.filter_subset _ _⟩
  calc f n ≤ _ := Finset.card_le_card hsub
    _ = 4 ^ (n - 1) := by
      rw [Finset.card_product, Finset.card_powerset, Finset.card_range, ← mul_pow]; norm_num

/-- **Exponential lower bound.** `4^(n-1) ≤ 2 (n-1) f n` for `n ≥ 2`. -/
theorem four_pow_le_f {n : ℕ} (hn : 2 ≤ n) : 4 ^ (n - 1) ≤ 2 * (n - 1) * f n := by
  have h := Nat.four_pow_le_two_mul_self_mul_centralBinom (n - 1) (by omega)
  rw [Nat.centralBinom_eq_two_mul_choose] at h
  exact h.trans (Nat.mul_le_mul_left _ (choose_le_f n))

end Stanley
