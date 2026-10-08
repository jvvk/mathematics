import EnclosingCopy.Enclosing.Regular
import EnclosingCopy.Enclosing.Polygon
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.MeasureTheory.Group.Measure

/-!
# Section 7: the region `R(t, Θ)` for the regular `q`-gon

In the normalisation of Section 7 (inradius 1, positions `s ∈ [-1, 1]`) every side has `hᵢ = 1`,
`aᵢ = -1`, `bᵢ = 1`, and normal `uⱼ = (cos (2πj/q), sin (2πj/q))`. The paper's region
`R(t, Θ) = {C : C · uᵢ ≤ t hᵢ + min (Θ aᵢ) (Θ bᵢ)}` is therefore `{C : C · uⱼ ≤ t - |Θ|}`.

* `R_eq_smul`: `R(t, Θ) = (t - |Θ|) • P` for `t > |Θ|`, with `P = R(1, 0)` the polygon itself;
* `volume_R`: `area R(t, Θ) = (t - |Θ|)² area P`;
* `width_R`: for even `q`, the projection of `R(t, Θ)` on `u₀` is `[-(t - |Θ|), t - |Θ|]`;
* `V_regular`: `∫∫ e^{-2qt} area R = area P / (4 q⁴)`;
* `volume_P_four`: for the square, `area P = 4 = 4 tan (π/4)`.
-/

namespace Enclosing

open MeasureTheory Set Real Pointwise

/-- Normal of side `j` of the regular `q`-gon. -/
noncomputable def un (q : ℕ) (j : Fin q) : ℝ × ℝ := (cos (2 * π * j / q), sin (2 * π * j / q))

/-- The region `R(t, Θ)` of Theorem 8 for the regular `q`-gon. -/
def Rreg (q : ℕ) (t Θ : ℝ) : Set (ℝ × ℝ) :=
  {C | ∀ j : Fin q, dot C (un q j) ≤ t * 1 + min (Θ * (-1)) (Θ * 1)}

/-- The regular `q`-gon of inradius 1. -/
def Preg (q : ℕ) : Set (ℝ × ℝ) := {C | ∀ j : Fin q, dot C (un q j) ≤ 1}

lemma min_neg_abs (Θ : ℝ) : min (Θ * (-1)) (Θ * 1) = -|Θ| := by
  rcases le_total 0 Θ with h | h
  · rw [abs_of_nonneg h, min_eq_left (by linarith)]; ring
  · rw [abs_of_nonpos h, min_eq_right (by linarith)]; ring

lemma dot_smul (c : ℝ) (C u : ℝ × ℝ) : dot (c • C) u = c * dot C u := by
  simp [dot]; ring

/-- `R(t, Θ) = (t - |Θ|) • P` when `t > |Θ|`. -/
theorem R_eq_smul (q : ℕ) {t Θ : ℝ} (h : |Θ| < t) : Rreg q t Θ = (t - |Θ|) • Preg q := by
  have hs : 0 < t - |Θ| := by linarith
  ext C
  simp only [Rreg, Preg]
  simp_rw [min_neg_abs, mul_one, mem_setOf_eq]
  rw [mem_smul_set_iff_inv_smul_mem₀ hs.ne']
  simp only [mem_setOf_eq, dot_smul]
  refine forall_congr' fun j => ?_
  rw [inv_mul_le_iff₀ hs, mul_one]
  constructor <;> intro h' <;> linarith

/-- `area R(t, Θ) = (t - |Θ|)² · area P`. -/
theorem volume_R (q : ℕ) {t Θ : ℝ} (h : |Θ| < t) :
    volume (Rreg q t Θ) = ENNReal.ofReal ((t - |Θ|) ^ 2) * volume (Preg q) := by
  rw [R_eq_smul q h, Measure.volume_eq_prod, Measure.addHaar_smul, Module.finrank_prod,
    Module.finrank_self, abs_of_nonneg (by positivity)]

/-- For even `q` the side opposite side `0` is side `q/2`, with normal `-u₀`. -/
lemma un_half {r : ℕ} (hr : 0 < r) :
    un (2 * r) ⟨r, by omega⟩ = (-1, 0) := by
  have : 2 * π * (r : ℝ) / (2 * (r : ℝ)) = π := by
    have : (0 : ℝ) < r := by exact_mod_cast hr
    field_simp
  simp [un, this]

lemma un_zero (q : ℕ) [NeZero q] : un q 0 = (1, 0) := by simp [un]

/-- For even `q`, the projection of `R(t, Θ)` on the direction `u₀` is the interval
`[-(t - |Θ|), t - |Θ|]`; its length `2 (t - |Θ|)` is the width in Theorem 8. -/
theorem width_R {r : ℕ} (hr : 0 < r) (t Θ : ℝ) :
    (fun C : ℝ × ℝ => C.1) '' Rreg (2 * r) t Θ = Icc (-(t - |Θ|)) (t - |Θ|) := by
  have : NeZero (2 * r) := ⟨by omega⟩
  ext w
  simp only [Rreg]
  simp_rw [min_neg_abs, mul_one, mem_image, mem_setOf_eq, mem_Icc]
  constructor
  · rintro ⟨C, hC, rfl⟩
    have h0 := hC 0
    have h1 := hC ⟨r, by omega⟩
    rw [un_zero] at h0
    rw [un_half hr] at h1
    simp only [dot] at h0 h1
    constructor <;> linarith
  · rintro ⟨hl, hu⟩
    refine ⟨(w, 0), fun j => ?_, rfl⟩
    simp only [un, dot]
    have hc := abs_le.1 (abs_cos_le_one (2 * π * j / (2 * r : ℕ)))
    rcases le_total 0 w with hw | hw
    · nlinarith
    · nlinarith

/-- **The vertex-term integral** `∫∫ e^{-2qt} area R(t, Θ) = area P / (4 q⁴)`. -/
theorem V_regular (q : ℕ) (hq : 0 < q) :
    ∫ Θ, ∫ t in Ioi |Θ|, exp (-(2 * q * t)) * (volume (Rreg q t Θ)).toReal
      = (volume (Preg q)).toReal / (4 * (q : ℝ) ^ 4) := by
  have hq' : (0 : ℝ) < q := by exact_mod_cast hq
  have : ∀ Θ, ∫ t in Ioi |Θ|, exp (-(2 * q * t)) * (volume (Rreg q t Θ)).toReal
      = (volume (Preg q)).toReal * ∫ t in Ioi |Θ|, exp (-(2 * q * t)) * (t - |Θ|) ^ 2 := by
    intro Θ
    rw [← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
    rw [volume_R q ht, ENNReal.toReal_mul, ENNReal.toReal_ofReal (sq_nonneg _)]
    ring
  simp_rw [this]
  rw [integral_const_mul, scale_tilt_area hq']
  ring

/-- The square: `P = [-1, 1]²`, of area `4 = 4 tan (π/4)`. -/
theorem volume_P_four : volume (Preg 4) = 4 := by
  have hP : Preg 4 = Icc (-1 : ℝ) 1 ×ˢ Icc (-1 : ℝ) 1 := by
    have c1 : cos (2 * π / 4) = 0 := by rw [show 2 * π / 4 = π / 2 by ring, cos_pi_div_two]
    have s1 : sin (2 * π / 4) = 1 := by rw [show 2 * π / 4 = π / 2 by ring, sin_pi_div_two]
    have c2 : cos (2 * π * 2 / 4) = -1 := by rw [show 2 * π * 2 / 4 = π by ring, cos_pi]
    have s2 : sin (2 * π * 2 / 4) = 0 := by rw [show 2 * π * 2 / 4 = π by ring, sin_pi]
    have c3 : cos (2 * π * 3 / 4) = 0 := by
      rw [show 2 * π * 3 / 4 = π / 2 + π by ring, cos_add_pi, cos_pi_div_two, neg_zero]
    have s3 : sin (2 * π * 3 / 4) = -1 := by
      rw [show 2 * π * 3 / 4 = π / 2 + π by ring, sin_add_pi, sin_pi_div_two]
    ext C
    simp only [Preg, un, dot, Fin.forall_fin_succ, IsEmpty.forall_iff, mem_setOf_eq, mem_prod,
      mem_Icc]
    simp [c1, s1, c2, s2, c3, s3]
    constructor
    · rintro ⟨h0, h1, h2, h3⟩; refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;> linarith
    · rintro ⟨⟨h0, h1⟩, h2, h3⟩; refine ⟨?_, ?_, ?_, ?_⟩ <;> linarith
  rw [hP, Measure.volume_eq_prod, Measure.prod_prod, Real.volume_Icc]
  norm_num

/-- **Segment term of Theorem 8 for the regular `2r`-gon, in measure form.** The width is the
Lebesgue length of the projection of `R(t, Θ)` on `u₀` and the area its Lebesgue area. Given the
classical area `q tan (π/q)` of the regular `q`-gon of inradius 1, the term is `8/(3q²)`. -/
theorem segment_term_measure {r : ℕ} (hr : 2 ≤ r)
    (hP : (volume (Preg (2 * r))).toReal = (2 * r : ℝ) * tan (π / (2 * r))) :
    let q : ℝ := 2 * r
    let S : ℝ := ∑ j ∈ Finset.Ico 1 r, 2 * sin (2 * π * j / q)
    q * (∫ x in (-1 : ℝ)..1, ∫ s₁ in (-1 : ℝ)..x, ∫ s₂ in x..1, (s₂ - s₁)) *
        (2 * (∫ Θ, ∫ t in Ioi |Θ|, exp (-(2 * q * t)) *
            (volume ((fun C : ℝ × ℝ => C.1) '' Rreg (2 * r) t Θ)).toReal)
          + 2 * S * ∫ Θ, ∫ t in Ioi |Θ|, exp (-(2 * q * t)) * (volume (Rreg (2 * r) t Θ)).toReal)
      = 8 / (3 * q ^ 2) := by
  intro q S
  have hr0 : 0 < r := by omega
  have hq : 0 < 2 * r := by omega
  have hwidth : ∀ Θ, ∫ t in Ioi |Θ|, exp (-(2 * q * t)) *
      (volume ((fun C : ℝ × ℝ => C.1) '' Rreg (2 * r) t Θ)).toReal
      = 2 * ∫ t in Ioi |Θ|, exp (-(2 * q * t)) * (t - |Θ|) ^ 1 := by
    intro Θ
    rw [← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
    rw [width_R hr0, Real.volume_Icc, ENNReal.toReal_ofReal (by linarith [show |Θ| < t from ht])]
    ring
  rw [integral_congr_ae (Filter.Eventually.of_forall hwidth), integral_const_mul]
  have hV := V_regular (2 * r) hq
  push_cast at hV
  rw [hV, hP]
  have h := segment_term_regular hr
  rw [← h, scale_tilt_area (by positivity : (0 : ℝ) < 2 * r)]
  ring

/-- **The square's segment term is `8/(3·4²) = 1/6`**, with no geometric input left. -/
theorem segment_term_square :
    4 * (∫ x in (-1 : ℝ)..1, ∫ s₁ in (-1 : ℝ)..x, ∫ s₂ in x..1, (s₂ - s₁)) *
        (2 * (∫ Θ, ∫ t in Ioi |Θ|, exp (-(2 * 4 * t)) *
            (volume ((fun C : ℝ × ℝ => C.1) '' Rreg 4 t Θ)).toReal)
          + 2 * (∑ j ∈ Finset.Ico (1 : ℕ) 2, 2 * sin (2 * π * j / 4)) *
            ∫ Θ, ∫ t in Ioi |Θ|, exp (-(2 * 4 * t)) * (volume (Rreg 4 t Θ)).toReal)
      = 1 / 6 := by
  have h := segment_term_measure (r := 2) le_rfl (by
    rw [volume_P_four]; norm_num [show π / (2 * 2) = π / 4 by ring, tan_pi_div_four])
  norm_num at h ⊢
  convert h using 2

end Enclosing
