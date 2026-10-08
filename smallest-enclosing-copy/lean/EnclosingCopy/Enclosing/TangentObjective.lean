import EnclosingCopy.Enclosing.TangentSimilarity
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Scale stability in exact tangent coordinates

The scale correction has an explicit quadratic bound. A linear objective gap
controlling the tilt gap preserves the entire optimal face on a bounded tilt
window, including faces with a free translation coordinate.
-/
namespace Enclosing
open Real Filter Topology

lemma tangent_sqrt_ge_one (t : ℝ) : 1 ≤ sqrt (1 + t ^ 2) := by
  simpa using sqrt_le_sqrt (show (1 : ℝ) ≤ 1 + t ^ 2 by nlinarith [sq_nonneg t])

lemma tangent_sqrt_sub_one_le (t : ℝ) : sqrt (1 + t ^ 2) - 1 ≤ t ^ 2 / 2 := by
  have he := sq_sqrt (show 0 ≤ 1 + t ^ 2 by positivity)
  have hs := tangent_sqrt_ge_one t
  nlinarith [sq_nonneg (sqrt (1 + t ^ 2) - 1)]

/-- A uniform bound for the difference between the physical and LP objectives. -/
theorem tangentScale_error {q R : ℝ} (hq : 0 < q) (hR : 0 ≤ R) (z : Copy)
    (he : |z.1| ≤ R) (ht : |z.2.2| ≤ R) :
    |(tangentScale q z - 1) / q - z.1| ≤ q * R ^ 2 * (1 + q * R) / 2 := by
  let s := sqrt (1 + (q * z.2.2) ^ 2)
  have hs : 1 ≤ s := tangent_sqrt_ge_one _
  have hsp : 0 < s := lt_of_lt_of_le (by norm_num) hs
  have hsq : s - 1 ≤ (q * z.2.2) ^ 2 / 2 := tangent_sqrt_sub_one_le _
  have he' : |1 + q * z.1| ≤ 1 + q * R := by
    calc _ ≤ |(1 : ℝ)| + |q * z.1| := abs_add_le _ _
      _ ≤ _ := by rw [abs_one, abs_mul, abs_of_pos hq]; gcongr
  have htsq : z.2.2 ^ 2 ≤ R ^ 2 := by
    simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg z.2.2) hR).mpr ht
  have hEq : (tangentScale q z - 1) / q - z.1 =
      -(1 + q * z.1) * (s - 1) / (q * s) := by
    dsimp [tangentScale, s]; field_simp; ring
  rw [hEq, abs_div, abs_mul, abs_neg, abs_of_nonneg (by linarith : 0 ≤ s - 1),
    abs_of_pos (mul_pos hq hsp), div_le_iff₀ (mul_pos hq hsp)]
  have h1 : |1 + q * z.1| * (s - 1) ≤
      (1 + q * R) * ((q * z.2.2) ^ 2 / 2) :=
    mul_le_mul he' hsq (by linarith) (by positivity)
  have h2 : (1 + q * R) * ((q * z.2.2) ^ 2 / 2) ≤
      (1 + q * R) * (q ^ 2 * R ^ 2 / 2) := by
    rw [mul_pow]
    gcongr
  have h3 := mul_le_mul_of_nonneg_left hs
    (show 0 ≤ q * R ^ 2 * (1 + q * R) / 2 * q by positivity)
  nlinarith

/-- The square-root scale factor is Lipschitz in bounded tilt coordinates. -/
lemma tangent_sqrt_lipschitz {q R t u : ℝ} (_hR : 0 ≤ R)
    (ht : |t| ≤ R) (hu : |u| ≤ R) :
    |sqrt (1 + (q * t) ^ 2) - sqrt (1 + (q * u) ^ 2)| ≤
      q ^ 2 * R * |t - u| := by
  let a := sqrt (1 + (q * t) ^ 2)
  let b := sqrt (1 + (q * u) ^ 2)
  have ha : 1 ≤ a := tangent_sqrt_ge_one _
  have hb : 1 ≤ b := tangent_sqrt_ge_one _
  have hea : a ^ 2 = 1 + (q * t) ^ 2 := sq_sqrt (by positivity)
  have heb : b ^ 2 = 1 + (q * u) ^ 2 := sq_sqrt (by positivity)
  have hEq : |a - b| * (a + b) = q ^ 2 * |t - u| * |t + u| := by
    calc
      _ = |(a - b) * (a + b)| := by
        rw [abs_mul, abs_of_nonneg (show 0 ≤ a + b by linarith)]
      _ = |q ^ 2 * ((t - u) * (t + u))| := by congr 1; nlinarith
      _ = _ := by rw [abs_mul, abs_of_nonneg (sq_nonneg q), abs_mul]; ring
  have hsum : |t + u| ≤ 2 * R := (abs_add_le t u).trans (by linarith)
  have h1 := mul_le_mul_of_nonneg_left hsum
    (show 0 ≤ q ^ 2 * |t - u| by positivity)
  have h2 := mul_le_mul_of_nonneg_left (show 2 ≤ a + b by linarith) (abs_nonneg (a - b))
  nlinarith

/-- A strict LP objective gap persists for the actual scale objective. -/
lemma tangentScale_strict_gap {q R D : ℝ} (hq : 0 < q) (hR : 0 ≤ R)
    (_hD : 0 ≤ D) (z zs : Copy) (ht : |z.2.2| ≤ R) (hts : |zs.2.2| ≤ R)
    (he : zs.1 < z.1) (hgap : |z.2.2 - zs.2.2| ≤ D * (z.1 - zs.1))
    (hsmall : q * R * D * |1 + q * zs.1| < 1) :
    tangentScale q zs < tangentScale q z := by
  let a := sqrt (1 + (q * z.2.2) ^ 2)
  let b := sqrt (1 + (q * zs.2.2) ^ 2)
  have ha : 0 < a := sqrt_pos.2 (by positivity)
  have hb : 0 < b := sqrt_pos.2 (by positivity)
  have hb1 : 1 ≤ b := tangent_sqrt_ge_one _
  have hroot : |a - b| ≤ q ^ 2 * R * |z.2.2 - zs.2.2| :=
    tangent_sqrt_lipschitz hR ht hts
  have h1 : (1 + q * zs.1) * (a - b) ≤ |1 + q * zs.1| * |a - b| := by
    simpa only [abs_mul] using le_abs_self ((1 + q * zs.1) * (a - b))
  have h2 := mul_le_mul_of_nonneg_left hroot (abs_nonneg (1 + q * zs.1))
  have h3 := mul_le_mul_of_nonneg_left hgap
    (show 0 ≤ |1 + q * zs.1| * (q ^ 2 * R) by positivity)
  have h4 := mul_lt_mul_of_pos_right hsmall (mul_pos hq (sub_pos.mpr he))
  have h5 := mul_le_mul_of_nonneg_left hb1 (mul_nonneg hq.le (sub_nonneg.mpr he.le))
  change (1 + q * zs.1) / b < (1 + q * z.1) / a
  rw [div_lt_div_iff₀ hb ha]
  nlinarith

/-- Exact objective equality on the LP face once the tilt gap is controlled. -/
lemma tangentScale_eq_of_objective_eq {D : ℝ} (z zs : Copy)
    (he : z.1 = zs.1) (hgap : |z.2.2 - zs.2.2| ≤ D * (z.1 - zs.1)) (q : ℝ) :
    tangentScale q z = tangentScale q zs := by
  have ht : z.2.2 = zs.2.2 := by
    rw [he, sub_self, mul_zero] at hgap
    exact sub_eq_zero.mp (abs_eq_zero.mp (le_antisymm hgap (abs_nonneg _)))
  simp only [tangentScale, he, ht]

/-- On a bounded tilt window, the physical scale and LP have exactly the same
optimal face for all sufficiently large sample sizes. -/
theorem tangentScale_optimal_face {R D : ℝ} (hR : 0 ≤ R) (hD : 0 ≤ D)
    (S : Set Copy) (zs : Copy) (_hzs : zs ∈ S) (hts : |zs.2.2| ≤ R)
    (hopt : ∀ z ∈ S, zs.1 ≤ z.1)
    (hgap : ∀ z ∈ S, |z.2.2 - zs.2.2| ≤ D * (z.1 - zs.1)) :
    ∀ᶠ n : ℕ in atTop, ∀ z ∈ S, |z.2.2| ≤ R →
      (tangentScale (1 / n) z ≤ tangentScale (1 / n) zs ↔ z.1 = zs.1) := by
  have hq : Tendsto (fun n : ℕ => (1 : ℝ) / n) atTop (𝓝 0) :=
    tendsto_const_div_atTop_nhds_zero_nat 1
  have hs : Tendsto (fun n : ℕ => (1 / n) * R * D * |1 + (1 / n) * zs.1|)
      atTop (𝓝 0) := by
    simpa using ((hq.mul_const R).mul_const D).mul
      ((tendsto_const_nhds.add (hq.mul_const zs.1)).abs)
  filter_upwards [hs.eventually (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1)),
    eventually_gt_atTop 0] with n hn hnpos z hz ht
  have hqn : 0 < (1 : ℝ) / n := one_div_pos.mpr (by exact_mod_cast hnpos)
  constructor
  · intro hle
    by_contra hne
    exact (not_lt_of_ge hle) (tangentScale_strict_gap hqn hR hD z zs ht hts
      (lt_of_le_of_ne (hopt z hz) (Ne.symm hne)) (hgap z hz) hn)
  · intro he
    exact (tangentScale_eq_of_objective_eq z zs he (hgap z hz) _).le

end Enclosing
