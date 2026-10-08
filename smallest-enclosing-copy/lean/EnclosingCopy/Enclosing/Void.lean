import EnclosingCopy.Enclosing.Polygon
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Integral
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Lemma 7 (void probability)

In the limit model side `i` carries a Poisson process of intensity 1 on the strip
`[aᵢ, bᵢ] × [0, ∞)` of points `(s, D)`. A copy with parameters `(ε, C, Θ)` has, on side `i`, the
line `D = Θ s - Hᵢ` with `Hᵢ = ε hᵢ + C · uᵢ`; a point violates the copy iff it lies between `D = 0`
and that line. The void probability of a Poisson process is `exp (-(area of the region))`, so
Lemma 7 is the statement that, under the event `Hᵢ ≤ min (Θ aᵢ) (Θ bᵢ)`, the regions have total
Lebesgue area `-2 ε · area K`. The `Θ` terms cancel by the telescoping identity (1c).
-/

namespace Enclosing

open MeasureTheory Finset

variable {m : ℕ} [NeZero m]

/-- The region of side `i` that a point must avoid: between `D = 0` and the line `D = Θ s - H`. -/
def voidRegion (a b Θ H : ℝ) : Set (ℝ × ℝ) :=
  regionBetween (fun _ => (0 : ℝ)) (fun s => Θ * s - H) (Set.Icc a b)

/-- Under the event the line is nonnegative on the side. -/
lemma line_nonneg {a b Θ H s : ℝ} (hH : H ≤ min (Θ * a) (Θ * b)) (hs : s ∈ Set.Icc a b) :
    0 ≤ Θ * s - H := by
  rcases le_total 0 Θ with hΘ | hΘ
  · have := mul_le_mul_of_nonneg_left hs.1 hΘ
    linarith [min_le_left (Θ * a) (Θ * b)]
  · have := mul_le_mul_of_nonpos_left hs.2 hΘ
    linarith [min_le_right (Θ * a) (Θ * b)]

/-- Area under the line on one side. -/
lemma integral_line (a b Θ H : ℝ) :
    ∫ s in a..b, (Θ * s - H) = Θ * (b ^ 2 - a ^ 2) / 2 - (b - a) * H := by
  rw [intervalIntegral.integral_sub (f := fun s => Θ * s) (g := fun _ => H)
    ((by fun_prop : Continuous fun s : ℝ => Θ * s).intervalIntegrable a b)
    intervalIntegrable_const, intervalIntegral.integral_const_mul]
  simp [integral_id]
  ring

lemma line_area_nonneg {a b Θ H : ℝ} (hab : a ≤ b) (hH : H ≤ min (Θ * a) (Θ * b)) :
    0 ≤ Θ * (b ^ 2 - a ^ 2) / 2 - (b - a) * H := by
  rw [← integral_line]
  exact intervalIntegral.integral_nonneg hab fun s hs => line_nonneg hH hs

/-- The area of one void region. -/
theorem volume_voidRegion {a b Θ H : ℝ} (hab : a ≤ b) (hH : H ≤ min (Θ * a) (Θ * b)) :
    volume (voidRegion a b Θ H) = ENNReal.ofReal (Θ * (b ^ 2 - a ^ 2) / 2 - (b - a) * H) := by
  unfold voidRegion
  rw [Measure.volume_eq_prod, volume_regionBetween_eq_integral (f := fun _ => (0 : ℝ))
      (g := fun s => Θ * s - H) (integrableOn_const (by simp))
      (by fun_prop : Continuous fun s : ℝ => Θ * s - H).integrableOn_Icc
      measurableSet_Icc (fun s hs => line_nonneg hH hs)]
  congr 1
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hab, ← integral_line]
  simp

/-- `Hᵢ = ε hᵢ + C · uᵢ`, the support of the copy's side `i` above the side of `K`. -/
noncomputable def Hcopy (v : Fin m → ℝ × ℝ) (ε : ℝ) (C : ℝ × ℝ) (i : Fin m) : ℝ :=
  ε * hsup v i + dot C (nrm v i)

/-- `∑ Lᵢ Hᵢ = 2 ε · area`, by identities (1a) and (1b). -/
theorem sum_len_Hcopy (v : Fin m → ℝ × ℝ) (hv : Nondeg v) (ε : ℝ) (C : ℝ × ℝ) :
    ∑ i, len v i * Hcopy v ε C i = 2 * ε * area v := by
  obtain ⟨h1, h2⟩ := sum_len_nrm v hv
  have := sum_len_hsup v hv
  simp only [Hcopy, dot, mul_add, sum_add_distrib]
  have e1 : ∑ i, len v i * (ε * hsup v i) = ε * ∑ i, len v i * hsup v i := by
    rw [mul_sum]; exact sum_congr rfl fun i _ => by ring
  have e2 : ∑ i, len v i * (C.1 * (nrm v i).1) = C.1 * ∑ i, len v i * (nrm v i).1 := by
    rw [mul_sum]; exact sum_congr rfl fun i _ => by ring
  have e3 : ∑ i, len v i * (C.2 * (nrm v i).2) = C.2 * ∑ i, len v i * (nrm v i).2 := by
    rw [mul_sum]; exact sum_congr rfl fun i _ => by ring
  rw [e1, e2, e3, h1, h2, this]
  ring

/-- **Lemma 7.** On the event `Hᵢ ≤ min (Θ aᵢ) (Θ bᵢ)` for all `i`, the void regions have total
area `-2 ε · area K`; hence the void probability `exp (-(total area))` equals `exp (2 ε · area K)`,
which is `exp (2 ε)` for `K` of area one. The rotation `Θ` drops out. -/
theorem void_area (v : Fin m → ℝ × ℝ) (hv : Nondeg v) (ε Θ : ℝ) (C : ℝ × ℝ)
    (hE : ∀ i, Hcopy v ε C i ≤ min (Θ * aEnd v i) (Θ * bEnd v i)) :
    ∑ i, (volume (voidRegion (aEnd v i) (bEnd v i) Θ (Hcopy v ε C i))).toReal
      = -(2 * ε * area v) := by
  have hab : ∀ i, aEnd v i ≤ bEnd v i := fun i => by
    have := len_pos v hv i; rw [len_eq_b_sub_a v hv] at this; linarith
  have hnn : ∀ i, 0 ≤ Θ * (bEnd v i ^ 2 - aEnd v i ^ 2) / 2 - (bEnd v i - aEnd v i) * Hcopy v ε C i :=
    fun i => line_area_nonneg (hab i) (hE i)
  simp_rw [fun i => volume_voidRegion (hab i) (hE i), fun i => ENNReal.toReal_ofReal (hnn i)]
  have htel : ∑ i, Θ * (bEnd v i ^ 2 - aEnd v i ^ 2) / 2 = 0 := by
    have : ∀ i, Θ * (bEnd v i ^ 2 - aEnd v i ^ 2) / 2
        = (Θ / 2) * (len v i * (aEnd v i + bEnd v i)) := fun i => by
      rw [len_eq_b_sub_a v hv]; ring
    simp_rw [this, len_mul_a_add_b v hv, ← mul_sum]
    rw [sum_shift_sub fun i => dot (v i) (v i), mul_zero]
  simp_rw [← len_eq_b_sub_a v hv]
  rw [sum_sub_distrib, htel, sum_len_Hcopy v hv]
  ring

end Enclosing
