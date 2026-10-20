import Mathlib
import LeanProofs.ProductTrajectory.Characters

/-!
# Product trajectories (Physics SE 816017), part 7: exponential sums

`χ_ν(t) = e^{-iνt}`. Two facts used for the maximally entangled theorem:

* `coeff_unique`: on a finite set of distinct frequencies, the coefficients of an exponential sum
  are
  determined by the function.
* `const_modulus_single`: an exponential sum (distinct frequencies, nonzero coefficients) of
  constant
  modulus has exactly one frequency.
-/

namespace ProductTrajectory

open Complex

/-- `e^{-iνt}`. -/
noncomputable def ch (ν t : ℝ) : ℂ := exp (-(I * (ν * t)))

theorem ch_eq_chi (ν : ℝ) (x : Multiplicative ℝ) : chi ν x = ch ν (Multiplicative.toAdd x) := rfl

theorem ch_mul (ν μ t : ℝ) : ch ν t * ch μ t = ch (ν + μ) t := by
  simp only [ch, ← Complex.exp_add]; congr 1; push_cast; ring

theorem conj_ch (ν t : ℝ) : (starRingEnd ℂ) (ch ν t) = ch (-ν) t := by
  simp only [ch, ← Complex.exp_conj]
  congr 1
  simp [map_neg, map_mul, conj_I, conj_ofReal]

theorem ch_zero (t : ℝ) : ch 0 t = 1 := by simp [ch]

/-- Linear independence of the characters, in finite-sum form. -/
theorem ch_indep (S : Finset ℝ) (g : ℝ → ℂ) (h : ∀ t : ℝ, ∑ s ∈ S, g s * ch s t = 0) :
    ∀ s ∈ S, g s = 0 := by
  have li := (linearIndependent_monoidHom (Multiplicative ℝ) ℂ).comp chi chi_injective
  rw [linearIndependent_iff'] at li
  refine li S g ?_
  funext x
  simpa [Finset.sum_apply, ch_eq_chi] using h (Multiplicative.toAdd x)

/-- **Uniqueness of coefficients.** -/
theorem coeff_unique (S : Finset ℝ) (c d : ℝ → ℂ)
    (h : ∀ t : ℝ, ∑ s ∈ S, c s * ch s t = ∑ s ∈ S, d s * ch s t) : ∀ s ∈ S, c s = d s := by
  intro s hs
  have := ch_indep S (fun s => c s - d s) (fun t => by
    simp only [sub_mul, Finset.sum_sub_distrib, h t, sub_self]) s hs
  exact sub_eq_zero.mp this

/-- A sum over pairs, grouped by the difference of frequencies, vanishes at every nonzero difference
if the pair sum is constant. -/
theorem pair_sum_const (S : Finset ℝ) (c : ℝ → ℂ) (K : ℂ)
    (h : ∀ t : ℝ, ∑ s ∈ S, ∑ s' ∈ S, c s * (starRingEnd ℂ) (c s') * ch (s - s') t = K)
    (δ : ℝ) (hδ : δ ≠ 0) :
    ∑ p ∈ (S ×ˢ S).filter (fun p => p.1 - p.2 = δ), c p.1 * (starRingEnd ℂ) (c p.2) = 0 := by
  classical
  set D := (S ×ˢ S).image (fun p => p.1 - p.2)
  set g : ℝ → ℂ := fun e => (∑ p ∈ (S ×ˢ S).filter (fun p => p.1 - p.2 = e),
    c p.1 * (starRingEnd ℂ) (c p.2)) - (if e = 0 then K else 0)
  by_cases hD : δ ∈ D
  · have key := ch_indep (insert 0 D) g (fun t => by
      have hsum : ∑ s ∈ S, ∑ s' ∈ S, c s * (starRingEnd ℂ) (c s') * ch (s - s') t =
          ∑ e ∈ insert 0 D, (∑ p ∈ (S ×ˢ S).filter (fun p => p.1 - p.2 = e),
            c p.1 * (starRingEnd ℂ) (c p.2)) * ch e t := by
        rw [← Finset.sum_product', ← Finset.sum_fiberwise_of_maps_to (g := fun p => p.1 - p.2)
          (t := insert 0 D) (fun p hp => Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ hp))]
        refine Finset.sum_congr rfl fun e _ => ?_
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl fun p hp => ?_
        rw [(Finset.mem_filter.mp hp).2]
      have hK : ∑ e ∈ insert 0 D, (if e = 0 then K else 0) * ch e t = K := by
        rw [Finset.sum_eq_single (0 : ℝ) (fun e _ he => by simp [he]) (fun h0 => absurd
          (Finset.mem_insert_self 0 D) h0)]
        simp [ch_zero]
      simp only [g, sub_mul, Finset.sum_sub_distrib]
      rw [← hsum, h t, hK, sub_self]) δ (Finset.mem_insert_of_mem hD)
    simpa [g, hδ] using key
  · rw [Finset.sum_eq_zero]
    intro p hp
    exact absurd (Finset.mem_image.mpr ⟨p, (Finset.mem_filter.mp hp).1,
        (Finset.mem_filter.mp hp).2⟩) hD

/-- **Constant modulus forces a single frequency.** -/
theorem const_modulus_single (S : Finset ℝ) (c : ℝ → ℂ) (hc : ∀ s ∈ S, c s ≠ 0) (hS : S.Nonempty)
    (K : ℝ) (h : ∀ t : ℝ, normSq (∑ s ∈ S, c s * ch s t) = K) : ∃ κ, S = {κ} := by
  classical
  set smax := S.max' hS
  set smin := S.min' hS
  refine ⟨smax, ?_⟩
  by_contra hne
  have hlt : smin < smax := by
    rcases (S.min'_le smax (S.max'_mem hS)).lt_or_eq with hl | he
    · exact hl
    · exfalso
      apply hne
      ext x
      simp only [Finset.mem_singleton]
      constructor
      · intro hx
        exact le_antisymm (S.le_max' x hx) (he ▸ S.min'_le x hx)
      · rintro rfl
        exact S.max'_mem hS
  have hpair : ∀ t : ℝ, ∑ s ∈ S, ∑ s' ∈ S,
      c s * (starRingEnd ℂ) (c s') * ch (s - s') t = (K : ℂ) := by
    intro t
    rw [← h t, Complex.normSq_eq_conj_mul_self, map_sum, Finset.sum_mul_sum, Finset.sum_comm]
    refine Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun s' _ => ?_
    rw [map_mul, conj_ch, show ch (s' - s) t = ch s' t * ch (-s) t by rw [ch_mul, sub_eq_add_neg]]
    ring
  have h0 := pair_sum_const S c K hpair (smax - smin) (by linarith)
  have hfib : (S ×ˢ S).filter (fun p => p.1 - p.2 = smax - smin) = {(smax, smin)} := by
    ext ⟨a, b⟩
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_singleton, Prod.mk.injEq]
    constructor
    · rintro ⟨⟨ha, hb⟩, hab⟩
      have h1 := S.le_max' a ha
      have h2 := S.min'_le b hb
      constructor <;> linarith
    · rintro ⟨rfl, rfl⟩
      exact ⟨⟨S.max'_mem hS, S.min'_mem hS⟩, rfl⟩
  rw [hfib, Finset.sum_singleton] at h0
  rcases mul_eq_zero.mp h0 with h1 | h1
  · exact hc _ (S.max'_mem hS) h1
  · exact hc _ (S.min'_mem hS) (by simpa using h1)

end ProductTrajectory
