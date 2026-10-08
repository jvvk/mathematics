import LeanProofs.Lemniscates.CaseIIb

/-!
# Theorem A

**Theorem A** (`theoremA`). Let `P₁, P₂ ∈ ℂ[z]` have degrees `n₁, n₂ ≥ 2` and `ρ₁, ρ₂ > 0`. If the
lemniscates `|P₁| = ρ₁` and `|P₂| = ρ₂` meet in finitely many points, they meet in at most
`2 n₁ n₂ - 2` points.

Write `P = λ f` with `f` monic. If `f₁, f₂` are coprime this is Case I (`CaseI.caseI`, the trace
identity and the pairing step); otherwise they share a root and Case II applies
(`CaseII.count_of_R_ne_zero` or `CaseII.empty_of_R_eq_zero`).

The corollaries (Cassini ovals, sharpness) are in `Corollaries.lean`.
-/

open Polynomial ComplexConjugate

namespace Lemniscates

open CaseI CaseII

lemma monic_part {P : ℂ[X]} (hP : P ≠ 0) :
    (P * C P.leadingCoeff⁻¹).Monic ∧ (P * C P.leadingCoeff⁻¹).natDegree = P.natDegree ∧
      ∀ z, P.eval z = P.leadingCoeff * (P * C P.leadingCoeff⁻¹).eval z := by
  have hl : P.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hP
  refine ⟨monic_mul_leadingCoeff_inv hP, natDegree_mul_C (inv_ne_zero hl), fun z => ?_⟩
  rw [eval_mul, eval_C, mul_comm (P.eval z), ← mul_assoc, mul_inv_cancel₀ hl, one_mul]

lemma norm_eq_iff_sq {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) : a = b ↔ a ^ 2 = b ^ 2 :=
  (pow_left_inj₀ ha hb two_ne_zero).symm

/-- **Theorem A.** -/
theorem theoremA (P₁ P₂ : ℂ[X]) (hn₁ : 2 ≤ P₁.natDegree) (hn₂ : 2 ≤ P₂.natDegree) {ρ₁ ρ₂ : ℝ}
    (hρ₁ : 0 < ρ₁) (hρ₂ : 0 < ρ₂)
    (hfin : {z : ℂ | ‖P₁.eval z‖ = ρ₁ ∧ ‖P₂.eval z‖ = ρ₂}.Finite) :
    hfin.toFinset.card ≤ 2 * P₁.natDegree * P₂.natDegree - 2 := by
  classical
  have hP₁ : P₁ ≠ 0 := by rintro rfl; simp at hn₁
  have hP₂ : P₂ ≠ 0 := by rintro rfl; simp at hn₂
  obtain ⟨hf₁, hd₁, he₁⟩ := monic_part hP₁
  obtain ⟨hf₂, hd₂, he₂⟩ := monic_part hP₂
  set f₁ := P₁ * C P₁.leadingCoeff⁻¹
  set f₂ := P₂ * C P₂.leadingCoeff⁻¹
  set l₁ := ‖P₁.leadingCoeff‖
  set l₂ := ‖P₂.leadingCoeff‖
  have hl₁ : 0 < l₁ := norm_pos_iff.mpr (leadingCoeff_ne_zero.mpr hP₁)
  have hl₂ : 0 < l₂ := norm_pos_iff.mpr (leadingCoeff_ne_zero.mpr hP₂)
  set r₁ := (ρ₁ / l₁) ^ 2
  set r₂ := (ρ₂ / l₂) ^ 2
  have hr₁ : 0 < r₁ := by positivity
  have hr₂ : 0 < r₂ := by positivity
  -- `|P| = ρ` iff `|f|² = (ρ / |λ|)²`
  have hiff : ∀ (P f : ℂ[X]) (l ρ : ℝ), 0 < l → 0 < ρ → (∀ z, ‖P.eval z‖ = l * ‖f.eval z‖) →
      ∀ z, ‖P.eval z‖ = ρ ↔ ‖f.eval z‖ ^ 2 = (ρ / l) ^ 2 := by
    intro P f l ρ hl hρ hPf z
    rw [hPf, ← norm_eq_iff_sq (norm_nonneg _) (by positivity), eq_div_iff hl.ne', mul_comm]
  have h₁ : ∀ z, ‖P₁.eval z‖ = l₁ * ‖f₁.eval z‖ := fun z => by rw [he₁ z, norm_mul]
  have h₂ : ∀ z, ‖P₂.eval z‖ = l₂ * ‖f₂.eval z‖ := fun z => by rw [he₂ z, norm_mul]
  have hset : {z : ℂ | ‖P₁.eval z‖ = ρ₁ ∧ ‖P₂.eval z‖ = ρ₂} =
      {z : ℂ | ‖f₁.eval z‖ ^ 2 = r₁ ∧ ‖f₂.eval z‖ ^ 2 = r₂} := by
    ext z
    simp only [Set.mem_ofPred_eq, hiff P₁ f₁ l₁ ρ₁ hl₁ hρ₁ h₁ z, hiff P₂ f₂ l₂ ρ₂ hl₂ hρ₂ h₂ z]
    exact Iff.rfl
  have hF : ∀ z ∈ hfin.toFinset, ‖f₁.eval z‖ ^ 2 = r₁ ∧ ‖f₂.eval z‖ ^ 2 = r₂ := by
    intro z hz
    rw [Set.Finite.mem_toFinset] at hz
    rw [hset] at hz
    exact hz
  rw [← hd₁, ← hd₂]
  rw [← hd₁] at hn₁
  rw [← hd₂] at hn₂
  by_cases hcop : IsCoprime f₁ f₂
  · exact caseI hf₁ hf₂ hn₁ hn₂ hcop hr₂.ne' _ hF
  -- a shared root
  rw [Polynomial.isCoprime_iff_aeval_ne_zero_of_isAlgClosed ℂ ℂ] at hcop
  push Not at hcop
  obtain ⟨ζ, hζ₁, hζ₂⟩ := hcop
  rw [coe_aeval_eq_eval] at hζ₁ hζ₂
  by_cases hR : R f₁ f₂ (conjP f₁) (conjP f₂) r₁ r₂ = 0
  · have hfin' := hfin
    rw [hset] at hfin'
    have hempty := empty_of_R_eq_zero hf₁ hf₂ (by omega) (by omega) hr₁ hr₂ hR hfin'
    have : hfin.toFinset = ∅ := by
      rw [Finset.eq_empty_iff_forall_notMem]
      intro z hz
      have := hF z hz
      have hz' : z ∈ {z : ℂ | ‖f₁.eval z‖ ^ 2 = r₁ ∧ ‖f₂.eval z‖ ^ 2 = r₂} := this
      rw [hempty] at hz'
      exact hz'
    rw [this, Finset.card_empty]
    exact Nat.zero_le _
  · exact count_of_R_ne_zero hf₁ hf₂ hn₁ hn₂ hζ₁ hζ₂ hR _ hF

end Lemniscates
