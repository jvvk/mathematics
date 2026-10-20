import Mathlib

/-!
# Product trajectories (Physics SE 816017), part 2: rank-one matrices over a GCD domain

A matrix over a GCD domain whose `2 × 2` minors all vanish is a column times a row, with both
factors in the ring (no denominators). Take `α` = a nonzero column divided by its gcd; every other
column is then a ring multiple of `α`.

This is Step 2 of the hand proof, used over `MvPolynomial (Fin k) ℂ`.
-/

namespace ProductTrajectory

open Finset Matrix

variable {R : Type*} [CommRing R] [IsDomain R] [NormalizedGCDMonoid R]
variable {ι κ : Type*} [Fintype ι] [Fintype κ]

/-- **Rank-one factorisation in the ring.** -/
theorem exists_vecMulVec_of_minors (F : Matrix ι κ R)
    (h : ∀ i i' l l', F i l * F i' l' = F i l' * F i' l) :
    ∃ (α : ι → R) (β : κ → R), F = vecMulVec α β := by
  classical
  by_cases hF : F = 0
  · exact ⟨0, 0, by ext i l; simp [hF, vecMulVec_apply]⟩
  obtain ⟨i₀, l₀, hne⟩ : ∃ i l, F i l ≠ 0 := by
    by_contra! hz
    exact hF (by ext i l; simp [hz i l])
  obtain ⟨α, hα, hg⟩ := extract_gcd (fun i => F i l₀) (univ_nonempty_iff.mpr ⟨i₀⟩)
  set d := univ.gcd (fun i => F i l₀) with hd_def
  have hd : d ≠ 0 := gcd_ne_zero_iff.mpr ⟨i₀, mem_univ _, hne⟩
  have hα' : ∀ i, F i l₀ = d * α i := fun i => hα i (mem_univ _)
  have hαi₀ : α i₀ ≠ 0 := by
    intro h0
    apply hne
    rw [hα' i₀, h0, mul_zero]
  -- every column is proportional to α
  have key : ∀ i i' l, F i l * α i' = α i * F i' l := by
    intro i i' l
    have := h i i' l l₀
    rw [hα' i', hα' i] at this
    exact mul_left_cancel₀ hd (by linear_combination this)
  have hdiv : ∀ l, α i₀ ∣ F i₀ l := by
    intro l
    have h1 : α i₀ ∣ univ.gcd (fun i' => F i₀ l * α i') :=
      dvd_gcd fun i' _ => ⟨F i' l, key i₀ i' l⟩
    have h2 := (gcd_mul_left' univ (fun i' => α i') (F i₀ l)).dvd
    rw [hg, mul_one] at h2
    exact h1.trans h2
  choose β hβ using hdiv
  refine ⟨α, β, ?_⟩
  ext i l
  rw [vecMulVec_apply]
  have := key i₀ i l
  rw [hβ l] at this
  exact mul_left_cancel₀ hαi₀ (by linear_combination -this)

end ProductTrajectory
