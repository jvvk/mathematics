import EnclosingCopy.Enclosing.Untruncated
import EnclosingCopy.Enclosing.TangentObjective
import EnclosingCopy.Enclosing.PolygonRegion

/-!
# Witness bounds for the exact physical scale problem

Once an angle is localized near a symmetry, shallow witnesses bound the scaled
tilt for every physical copy of scale at most one. No LP scale-sign assumption
is used: tangent coordinates have a small positive scale correction.
-/
namespace Enclosing
open Set Real
variable {m : ℕ} [NeZero m] (K : Sides m)

/-- Witness constraints bound tilt even when the tangent LP scale is positive. -/
lemma tilt_weighted_bound (wp wm : Fin m → Pt m) (hps : ∀ i, (wp i).1 = i) (hms : ∀ i, (wm i).1 = i)
    (hpp : ∀ i, K.b i - δK K ≤ (wp i).2.1) (hmm : ∀ i, (wm i).2.1 ≤ K.a i + δK K)
    (hpD : ∀ i, 0 ≤ (wp i).2.2) (hmD : ∀ i, 0 ≤ (wm i).2.2)
    (z : Copy) (hp : ∀ i, ¬ violates K z (wp i)) (hm : ∀ i, ¬ violates K z (wm i)) :
    |z.2.2| * Qs K ≤ 4 * z.1 +
      2 * (∑ i, Ls K i * ((wp i).2.2 + (wm i).2.2)) := by
  set Θ := z.2.2
  have hQ := Qs_pos K
  have hsum := sum_Ls_Hs K z
  have hDp : 0 ≤ ∑ i, Ls K i * (wp i).2.2 :=
    Finset.sum_nonneg fun i _ => mul_nonneg (Ls_pos K i).le (hpD i)
  have hDm : 0 ≤ ∑ i, Ls K i * (wm i).2.2 :=
    Finset.sum_nonneg fun i _ => mul_nonneg (Ls_pos K i).le (hmD i)
  have hsplit : ∑ i, Ls K i * ((wp i).2.2 + (wm i).2.2) =
      ∑ i, Ls K i * (wp i).2.2 + ∑ i, Ls K i * (wm i).2.2 := by
    rw [← Finset.sum_add_distrib]; exact Finset.sum_congr rfl fun i _ => by ring
  rw [hsplit]
  rcases le_total 0 Θ with hΘ | hΘ
  · have h1 : ∀ i, Ls K i * (Θ * (K.b i - δK K) - (wp i).2.2) ≤ Ls K i * Hs K z i := by
      intro i
      have := Hs_ge_of_not_violates K (hp i)
      rw [hps i] at this
      exact mul_le_mul_of_nonneg_left (by nlinarith [hpp i]) (Ls_pos K i).le
    have h2 := Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) => h1 i
    have e : ∀ i, Ls K i * (Θ * (K.b i - δK K) - (wp i).2.2) =
        Θ * (Ls K i * K.b i) - Θ * δK K * Ls K i - Ls K i * (wp i).2.2 := fun i => by ring
    simp_rw [e, Finset.sum_sub_distrib, ← Finset.mul_sum, sum_Ls_b] at h2
    rw [hsum] at h2
    have hper := δK_per K
    unfold per at hper
    rw [abs_of_nonneg hΘ]
    nlinarith
  · have h1 : ∀ i, Ls K i * (Θ * (K.a i + δK K) - (wm i).2.2) ≤ Ls K i * Hs K z i := by
      intro i
      have := Hs_ge_of_not_violates K (hm i)
      rw [hms i] at this
      exact mul_le_mul_of_nonneg_left (by nlinarith [hmm i]) (Ls_pos K i).le
    have h2 := Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) => h1 i
    have e : ∀ i, Ls K i * (Θ * (K.a i + δK K) - (wm i).2.2) =
        Θ * (Ls K i * K.a i) + Θ * δK K * Ls K i - Ls K i * (wm i).2.2 := fun i => by ring
    simp_rw [e, Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, sum_Ls_a] at h2
    rw [hsum] at h2
    have hper := δK_per K
    unfold per at hper
    rw [abs_of_nonpos hΘ]
    nlinarith


/-- Physical scale at most one allows only a quadratic positive LP scale. -/
lemma tangent_eps_upper {q : ℝ} (hq : 0 < q) (z : Copy)
    (hscale : tangentScale q z ≤ 1) : z.1 ≤ q * z.2.2 ^ 2 / 2 := by
  have hs : 0 < sqrt (1 + (q * z.2.2) ^ 2) := sqrt_pos.2 (by positivity)
  unfold tangentScale at hscale
  rw [div_le_iff₀ hs] at hscale
  have hb := tangent_sqrt_sub_one_le (q * z.2.2)
  have hmul : q * z.1 ≤ q * (q * z.2.2 ^ 2 / 2) := by nlinarith
  nlinarith

/-- Exact finite-scale tilt localization from shallow side witnesses. -/
theorem finite_tangent_tilt_bound (wp wm : Fin m → Pt m) (hW : Wit K wp wm)
    {q : ℝ} (hq : 0 < q) (z : Copy) (hscale : tangentScale q z ≤ 1)
    (hsmall : |q * z.2.2| ≤ Qs K / 4)
    (hp : ∀ i, ¬ violates K z (wp i)) (hm : ∀ i, ¬ violates K z (wm i)) :
    |z.2.2| ≤ 4 * (∑ i, Ls K i * ((wp i).2.2 + (wm i).2.2)) / Qs K := by
  have hb := tilt_weighted_bound K wp wm hW.ps hW.ms hW.pp hW.mm hW.pD hW.mD z hp hm
  have he := tangent_eps_upper hq z hscale
  rw [abs_mul, abs_of_pos hq] at hsmall
  have h1 := mul_le_mul_of_nonneg_right hsmall (abs_nonneg z.2.2)
  have hsq : |z.2.2| ^ 2 = z.2.2 ^ 2 := sq_abs _
  rw [le_div_iff₀ (Qs_pos K)]
  nlinarith

/-- Uniform witness depth gives a polygon-dependent tilt bound. -/
theorem finite_tangent_tilt_depth_bound (wp wm : Fin m → Pt m) (hW : Wit K wp wm)
    {q M : ℝ} (hq : 0 < q) (_hM : 0 ≤ M)
    (hDp : ∀ i, (wp i).2.2 ≤ M) (hDm : ∀ i, (wm i).2.2 ≤ M)
    (z : Copy) (hscale : tangentScale q z ≤ 1) (hsmall : |q * z.2.2| ≤ Qs K / 4)
    (hp : ∀ i, ¬ violates K z (wp i)) (hm : ∀ i, ¬ violates K z (wm i)) :
    |z.2.2| ≤ 8 * M * per K / Qs K := by
  have hb := finite_tangent_tilt_bound K wp wm hW hq z hscale hsmall hp hm
  have hs : ∑ i, Ls K i * ((wp i).2.2 + (wm i).2.2) ≤ 2 * M * per K := by
    unfold per
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    have h := mul_le_mul_of_nonneg_left (show (wp i).2.2 + (wm i).2.2 ≤ 2 * M by
      linarith [hDp i, hDm i]) (Ls_pos K i).le
    nlinarith
  exact hb.trans (by apply div_le_div_of_nonneg_right _ (Qs_pos K).le; nlinarith)

omit [NeZero m] in
lemma sum_Ls_dot (C : ℝ × ℝ) : ∑ i, Ls K i * dot C (K.u i) = 0 := by
  simp only [dot, mul_add, Finset.sum_add_distrib]
  have h1 : ∑ i, Ls K i * (C.1 * (K.u i).1) = 0 := by
    rw [show (0 : ℝ) = C.1 * 0 by ring, ← K.sum_u1, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _; dsimp [Ls]; ring
  have h2 : ∑ i, Ls K i * (C.2 * (K.u i).2) = 0 := by
    rw [show (0 : ℝ) = C.2 * 0 by ring, ← K.sum_u2, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _; dsimp [Ls]; ring
  rw [h1, h2, add_zero]

/-- Positive balancing weights turn lower normal bounds into two-sided bounds. -/
lemma balanced_normal_abs_bound (C : ℝ × ℝ) {A : ℝ} (hA : 0 ≤ A)
    (hlow : ∀ i, -A ≤ dot C (K.u i)) (i : Fin m) :
    |dot C (K.u i)| ≤ A + A * per K / Ls K i := by
  have hs : ∑ j, Ls K j * (dot C (K.u j) + A) = A * per K := by
    simp only [mul_add, Finset.sum_add_distrib, sum_Ls_dot, zero_add, per]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl; intro j _; ring
  have hsingle := Finset.single_le_sum
    (s := Finset.univ) (f := fun j => Ls K j * (dot C (K.u j) + A))
    (fun j _ => mul_nonneg (Ls_pos K j).le (by linarith [hlow j])) (Finset.mem_univ i)
  rw [hs] at hsingle
  have hu : dot C (K.u i) + A ≤ A * per K / Ls K i := by
    rw [le_div_iff₀ (Ls_pos K i)]; nlinarith
  have hp : 0 ≤ A * per K / Ls K i := by positivity [per_pos K, Ls_pos K i]
  rw [abs_le]
  constructor <;> linarith [hlow i]

/-- In a localized physical angle window, all four scaled coordinates of every
feasible scale-at-most-one copy are bounded by its shallow witness depths. -/
theorem finite_tangent_copy_bound (hG : GoodSides K) {M : ℝ} (hM : 0 ≤ M) :
    ∃ ρ ≥ 0, ∀ wp wm : Fin m → Pt m, Wit K wp wm →
      (∀ i, (wp i).2.2 ≤ M) → (∀ i, (wm i).2.2 ≤ M) → ∀ q : ℝ, 0 < q → q ≤ 1 → ∀ z : Copy,
      tangentScale q z ≤ 1 → |q * z.2.2| ≤ Qs K / 4 →
      (∀ i, ¬ violates K z (wp i)) → (∀ i, ¬ violates K z (wm i)) →
      |z.1| ≤ ρ ∧ |z.2.1.1| ≤ ρ ∧ |z.2.1.2| ≤ ρ ∧ |z.2.2| ≤ ρ := by
  let B := 8 * M * per K / Qs K
  have hB : 0 ≤ B := by dsimp [B]; positivity [per_pos K, Qs_pos K]
  let E := (B * Sb K + M) * per K / 2 + B ^ 2 / 2
  have hSb : 0 ≤ Sb K := Finset.sum_nonneg fun i _ => by positivity
  have hE : 0 ≤ E := by dsimp [E]; positivity [per_pos K]
  let H := ∑ i, |K.h i|
  have hH : 0 ≤ H := Finset.sum_nonneg fun _ _ => abs_nonneg _
  let A := B * Sb K + M + E * H
  have hA : 0 ≤ A := by dsimp [A]; positivity
  obtain ⟨j, hj⟩ := hG.nondeg (0 : Fin m)
  let U := A + A * per K / Ls K 0
  let V := A + A * per K / Ls K j
  have hU : 0 ≤ U := by dsimp [U]; positivity [per_pos K, Ls_pos K 0]
  have hV : 0 ≤ V := by dsimp [V]; positivity [per_pos K, Ls_pos K j]
  let C := (U * (|(K.u j).1| + |(K.u j).2|) +
    V * (|(K.u 0).1| + |(K.u 0).2|)) /
      |(K.u 0).1 * (K.u j).2 - (K.u 0).2 * (K.u j).1|
  have hC : 0 ≤ C := by dsimp [C]; positivity
  refine ⟨B + E + C, by positivity, ?_⟩
  intro wp wm hW hDp hDm q hq hq1 z hscale hsmall hp hm
  have ht : |z.2.2| ≤ B :=
    finite_tangent_tilt_depth_bound K wp wm hW hq hM hDp hDm z hscale hsmall hp hm
  have hpos (i : Fin m) : |(wp i).2.1| ≤ Sb K :=
    (abs_le_of_mem_Icc (hW.pI i)).trans (single_le_Sb K i)
  have hg (i : Fin m) : -(B * Sb K + M) ≤ Hs K z i := by
    have h := Hs_ge_of_not_violates K (hp i)
    rw [hW.ps i] at h
    have htprod : |z.2.2 * (wp i).2.1| ≤ B * Sb K := by
      rw [abs_mul]; exact mul_le_mul ht (hpos i) (abs_nonneg _) hB
    linarith [neg_abs_le (z.2.2 * (wp i).2.1), hDp i]
  have hsum := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) =>
    mul_le_mul_of_nonneg_left (hg i) (Ls_pos K i).le)
  rw [sum_Ls_Hs] at hsum
  have hsumleft : ∑ i, Ls K i * -(B * Sb K + M) = -(B * Sb K + M) * per K := by
    simp only [per, Finset.mul_sum]; apply Finset.sum_congr rfl; intro i _; ring
  rw [hsumleft] at hsum
  have htsq : z.2.2 ^ 2 ≤ B ^ 2 := by
    simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg z.2.2) hB).mpr ht
  have heupper := tangent_eps_upper hq z hscale
  have hqe := mul_le_mul_of_nonneg_right hq1 (sq_nonneg z.2.2)
  have hbase : 0 ≤ (B * Sb K + M) * per K := by positivity [per_pos K]
  have he : |z.1| ≤ E := by rw [abs_le]; dsimp [E]; constructor <;> nlinarith
  have hnormal (i : Fin m) : -A ≤ dot z.2.1 (K.u i) := by
    have hhi : |K.h i| ≤ H := Finset.single_le_sum
      (f := fun j => |K.h j|) (fun _ _ => abs_nonneg _) (Finset.mem_univ i)
    have hmul : |z.1 * K.h i| ≤ E * H := by
      rw [abs_mul]; exact mul_le_mul he hhi (abs_nonneg _) hE
    have hh := hg i
    unfold Hs at hh
    dsimp [A]
    linarith [le_abs_self (z.1 * K.h i)]
  have hc := coords_bounded (K.u 0) (K.u j) z.2.1 hj U V
    (balanced_normal_abs_bound K z.2.1 hA hnormal 0)
    (balanced_normal_abs_bound K z.2.1 hA hnormal j)
  exact ⟨by linarith, by linarith [hc.1], by linarith [hc.2], by linarith⟩

end Enclosing
