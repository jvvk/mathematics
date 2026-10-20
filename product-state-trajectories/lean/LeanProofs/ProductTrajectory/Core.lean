import Mathlib
import LeanProofs.ProductTrajectory.Graded
import LeanProofs.ProductTrajectory.RankOne

/-!
# Product trajectories (Physics SE 816017), part 3: the algebraic core

`F` is a matrix over `P = ℂ[X₁, …, X_k]` whose coefficient matrices `N_s` (the coefficient of `X^s`
in every entry) are pairwise orthogonal in the Frobenius inner product, and whose `2 × 2` minors
vanish. Then `F = α βᵀ` with `α, β` polynomial vectors whose own coefficient vectors are pairwise
orthogonal.

Proof (Steps 2–4' of the hand proof). Factor `F = α βᵀ` in `P` (part 2). In `Q = ℂ[u₁, …, u_k, v₁,
…, v_k]` put `G γ = ∑ᵢ γ̄ᵢ(u) γᵢ(v)`, so that the coefficient of `u^μ v^ν` in `G γ` is `∑ᵢ
conj(coeff_μ γᵢ) · coeff_ν γᵢ`. Then `G α · G β = G F`, and orthogonality makes `G F` homogeneous of
weight `0` for each grading `u_j ↦ -1, v_j ↦ +1`. By part 1, `G α` is homogeneous; its diagonal
coefficients `∑ᵢ |coeff_μ αᵢ|²` force weight `0`, which kills every off-diagonal coefficient.
-/

namespace ProductTrajectory

open MvPolynomial Finsupp Matrix

variable {k : ℕ}

/-- The conjugated copy of a polynomial in the `u` variables. -/
noncomputable def U : MvPolynomial (Fin k) ℂ →+* MvPolynomial (Fin k ⊕ Fin k) ℂ :=
  (rename Sum.inl).toRingHom.comp (map (starRingEnd ℂ))

/-- The copy of a polynomial in the `v` variables. -/
noncomputable def V : MvPolynomial (Fin k) ℂ →+* MvPolynomial (Fin k ⊕ Fin k) ℂ :=
  (rename Sum.inr).toRingHom

theorem sumElim_eq_sumElim_iff (μ ν μ' ν' : Fin k →₀ ℕ) :
    sumElim μ ν = sumElim μ' ν' ↔ μ = μ' ∧ ν = ν' := by
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · have := congrArg (fun c => comapDomain Sum.inl c Sum.inl_injective.injOn) h
      simpa [comapDomain_inl_sumElim] using this
    · have := congrArg (fun c => comapDomain Sum.inr c Sum.inr_injective.injOn) h
      simpa using this
  · rintro ⟨rfl, rfl⟩
    rfl

theorem coeff_U_mul_V (p q : MvPolynomial (Fin k) ℂ) (μ ν : Fin k →₀ ℕ) :
    (U p * V q).coeff (sumElim μ ν) = star (p.coeff μ) * q.coeff ν := by
  classical
  induction p using MvPolynomial.induction_on' with
  | monomial s a =>
    induction q using MvPolynomial.induction_on' with
    | monomial s' b =>
      simp only [U, V, RingHom.coe_comp, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
        Function.comp_apply, map_monomial, rename_monomial, monomial_mul_monomial, coeff_monomial,
        ← sumElim_eq_add, sumElim_eq_sumElim_iff]
      by_cases h1 : s = μ <;> by_cases h2 : s' = ν <;> simp [h1, h2]
    | add q₁ q₂ h₁ h₂ => simp [mul_add, h₁, h₂]
  | add p₁ p₂ h₁ h₂ => simp [add_mul, h₁, h₂]

/-- `G γ = ∑ⱼ γ̄ⱼ(u) γⱼ(v)`. -/
noncomputable def G {J : Type*} [Fintype J] (γ : J → MvPolynomial (Fin k) ℂ) :
    MvPolynomial (Fin k ⊕ Fin k) ℂ :=
  ∑ j, U (γ j) * V (γ j)

theorem coeff_G {J : Type*} [Fintype J] (γ : J → MvPolynomial (Fin k) ℂ) (μ ν : Fin k →₀ ℕ) :
    (G γ).coeff (sumElim μ ν) = ∑ j, star ((γ j).coeff μ) * (γ j).coeff ν := by
  simp [G, coeff_U_mul_V]

/-- The grading `u_j ↦ -1`, `v_j ↦ +1`, all other variables `0`. -/
def wt (j : Fin k) : Fin k ⊕ Fin k → ℤ :=
  Sum.elim (fun i => if i = j then -1 else 0) (fun i => if i = j then 1 else 0)

theorem weight_wt_sumElim (j : Fin k) (μ ν : Fin k →₀ ℕ) :
    weight (wt j) (sumElim μ ν) = (ν j : ℤ) - μ j := by
  classical
  rw [sumElim_eq_add, map_add, weight_apply, weight_apply,
    sum_mapDomain_index (by simp) (by intros; ring),
    sum_mapDomain_index (by simp) (by intros; ring)]
  simp only [wt, Sum.elim_inl, Sum.elim_inr, smul_ite, smul_neg, smul_zero, nsmul_eq_mul, mul_one]
  rw [Finsupp.sum_ite_eq', Finsupp.sum_ite_eq']
  by_cases hμ : j ∈ μ.support <;> by_cases hν : j ∈ ν.support <;>
    simp_all [Finsupp.mem_support_iff]
  ring

theorem sumElim_comap (d : Fin k ⊕ Fin k →₀ ℕ) :
    ∃ μ ν : Fin k →₀ ℕ, d = sumElim μ ν :=
  ⟨_, _, (comapDomain_sumElim_comapDomain d).symm⟩

theorem sum_star_mul_self_eq_zero {J : Type*} [Fintype J] (c : J → ℂ)
    (h : ∑ j, star (c j) * c j = 0) (j : J) : c j = 0 := by
  have e : ∀ j, star (c j) * c j = ((Complex.normSq (c j) : ℝ) : ℂ) := fun j => by
    rw [Complex.normSq_eq_conj_mul_self]; rfl
  simp_rw [e] at h
  rw [← Complex.ofReal_sum, Complex.ofReal_eq_zero] at h
  have := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => Complex.normSq_nonneg (c j))).mp h j
    (Finset.mem_univ _)
  exact Complex.normSq_eq_zero.mp this

/-- A nonzero vector has a nonzero diagonal coefficient in `G`. -/
theorem exists_diag {J : Type*} [Fintype J] {γ : J → MvPolynomial (Fin k) ℂ} (hγ : γ ≠ 0) :
    ∃ μ, (G γ).coeff (sumElim μ μ) ≠ 0 := by
  obtain ⟨j, hj⟩ := Function.ne_iff.mp hγ
  obtain ⟨μ, hμ⟩ := ne_zero_iff.mp hj
  refine ⟨μ, fun h0 => hμ ?_⟩
  rw [coeff_G] at h0
  exact sum_star_mul_self_eq_zero (fun j => (γ j).coeff μ) h0 j

/-- If `G γ` is homogeneous for every grading `wt j`, the coefficient vectors of `γ` are
orthogonal. -/
theorem orthogonal_of_homogeneous {J : Type*} [Fintype J] {γ : J → MvPolynomial (Fin k) ℂ}
    (hγ : γ ≠ 0) (h : ∀ j, ∃ c, IsWeightedHomogeneous (wt j) (G γ) c) :
    ∀ μ ν, μ ≠ ν → ∑ i, star ((γ i).coeff μ) * (γ i).coeff ν = 0 := by
  obtain ⟨μ₀, hμ₀⟩ := exists_diag hγ
  intro μ ν hne
  by_contra hs
  rw [← coeff_G] at hs
  apply hne
  ext j
  obtain ⟨c, hc⟩ := h j
  have h0 := hc hμ₀
  have h1 := hc hs
  rw [weight_wt_sumElim] at h0 h1
  omega

/-- **The algebraic core.** -/
theorem core {ι κ : Type*} [Fintype ι] [Fintype κ] (F : Matrix ι κ (MvPolynomial (Fin k) ℂ))
    (hminor : ∀ i i' l l', F i l * F i' l' = F i l' * F i' l)
    (horth : ∀ s s', s ≠ s' → ∑ i, ∑ l, star ((F i l).coeff s) * (F i l).coeff s' = 0) :
    ∃ (α : ι → MvPolynomial (Fin k) ℂ) (β : κ → MvPolynomial (Fin k) ℂ), F = vecMulVec α β ∧
      (∀ μ ν, μ ≠ ν → ∑ i, star ((α i).coeff μ) * (α i).coeff ν = 0) ∧
      (∀ μ ν, μ ≠ ν → ∑ l, star ((β l).coeff μ) * (β l).coeff ν = 0) := by
  classical
  let _ : StrongNormalizationMonoid (MvPolynomial (Fin k) ℂ) :=
    UniqueFactorizationMonoid.strongNormalizationMonoid
  let _ := UniqueFactorizationMonoid.toNormalizedGCDMonoid (MvPolynomial (Fin k) ℂ)
  obtain ⟨α, β, hF⟩ := exists_vecMulVec_of_minors F hminor
  -- degenerate case: F = 0
  by_cases hz : α = 0 ∨ β = 0
  · refine ⟨0, 0, ?_, by simp, by simp⟩
    rcases hz with h | h <;> (ext i l; simp [hF, h, vecMulVec_apply])
  push Not at hz
  obtain ⟨hα, hβ⟩ := hz
  -- G α * G β = G F
  have hGF : G α * G β = G (fun x : ι × κ => F x.1 x.2) := by
    simp only [G, Finset.sum_mul_sum, Fintype.sum_prod_type, hF, vecMulVec_apply, map_mul]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun l _ => ?_
    ring
  -- G F is homogeneous of weight 0 for every grading
  have hhom : ∀ j, IsWeightedHomogeneous (wt j) (G α * G β) 0 := by
    intro j d hd
    obtain ⟨μ, ν, rfl⟩ := sumElim_comap d
    rw [hGF, coeff_G, Fintype.sum_prod_type] at hd
    have hμν : μ = ν := by
      by_contra hne
      exact hd (horth μ ν hne)
    subst hμν
    rw [weight_wt_sumElim]
    simp
  have hGα : G α ≠ 0 := fun h0 => by
    obtain ⟨μ, hμ⟩ := exists_diag hα
    exact hμ (by rw [h0]; simp)
  have hGβ : G β ≠ 0 := fun h0 => by
    obtain ⟨μ, hμ⟩ := exists_diag hβ
    exact hμ (by rw [h0]; simp)
  refine ⟨α, β, hF, ?_, ?_⟩
  · exact orthogonal_of_homogeneous hα fun j =>
      isWeightedHomogeneous_of_mul (wt j) hGα hGβ (hhom j)
  · refine orthogonal_of_homogeneous hβ fun j =>
      isWeightedHomogeneous_of_mul (wt j) hGβ hGα (m := 0) ?_
    rw [mul_comm]
    exact hhom j

end ProductTrajectory
