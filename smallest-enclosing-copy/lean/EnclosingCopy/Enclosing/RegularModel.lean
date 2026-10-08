import EnclosingCopy.Enclosing.SquareSegment
import EnclosingCopy.Enclosing.RegularArea
import EnclosingCopy.Enclosing.GeneralClassify
import EnclosingCopy.Enclosing.Tetrahedron
import EnclosingCopy.Enclosing.RegularPolygon

/-!
# Theorem 8 for the regular `q`-gon (Section 7)

For side data with the normals `uⱼ = (cos θⱼ, sin θⱼ)` of the regular `q`-gon, support numbers `r`
and positions `[-c, c]` (`IsReg K r c`), the three factors of Theorem 8 are explicit.

* `spatial_reg`: the fitting region at scale `t` and tilt `θ` is `ρ P` with `ρ = r t - c|θ|`
  and `area P = q tan (π/q)`, so the spatial integral is `q tan(π/q) r³ / (4c)`.
* `cone_reg`: the rows of the vertex matrix are `(r, uⱼ, c y)` with `s = -c y`, so
  `|det A| = r c |det M|` for the homogeneous matrix `M` of the prism points `(uⱼ, y)`, and the
  KKT cone condition says that the origin is a positive combination of them. By `tetW_eq` the cone
  density is `4 r c⁵ q⁴ E[Vol(T) 1{0 ∈ int T}]`, the expectation over four independent points,
  each on a uniformly chosen vertical edge of the prism `P_q × [-1, 1]` at a uniform height.
-/

namespace Enclosing

open MeasureTheory Set Real ENNReal
open scoped Pointwise

variable {q : ℕ}

/-- Side data of the regular `q`-gon with support numbers `r` and positions `[-c, c]`. -/
structure IsReg (K : Sides q) (r c : ℝ) : Prop where
  u : ∀ j, K.u j = un q j
  h : ∀ j, K.h j = r
  a : ∀ j, K.a j = -c
  b : ∀ j, K.b j = c

/-- `∫ e^{-k|θ|}` is finite. -/
lemma integrable_exp_neg_abs_mul {k : ℝ} (hk : 0 < k) : Integrable fun θ : ℝ => exp (-(k * |θ|)) := by
  rw [← integrableOn_univ, ← Iic_union_Ioi (a := (0 : ℝ))]
  refine IntegrableOn.union ?_ ?_
  · refine (integrableOn_exp_mul_Iic (a := k) hk 0).congr_fun (fun θ hθ => ?_) measurableSet_Iic
    rw [abs_of_nonpos (mem_Iic.1 hθ)]; ring_nf
  · refine (integrableOn_exp_mul_Ioi (a := -k) (by linarith) 0).congr_fun (fun θ hθ => ?_)
      measurableSet_Ioi
    rw [abs_of_pos (mem_Ioi.1 hθ)]; ring_nf

/-- `∫⁻ e^{-k|θ|} = 2/k`. -/
lemma lintegral_exp_neg_abs {k : ℝ} (hk : 0 < k) :
    ∫⁻ θ : ℝ, ENNReal.ofReal (exp (-(k * |θ|))) = ENNReal.ofReal (2 / k) := by
  rw [← ofReal_integral_eq_lintegral_ofReal (integrable_exp_neg_abs_mul hk)
    (Filter.Eventually.of_forall fun θ => (exp_pos _).le), integral_exp_neg_abs hk]

lemma min_neg_c {c : ℝ} (hc : 0 ≤ c) (θ : ℝ) : min (θ * -c) (θ * c) = -(c * |θ|) := by
  rcases le_total 0 θ with h | h
  · rw [abs_of_nonneg h, min_eq_left (by nlinarith)]; ring
  · rw [abs_of_nonpos h, min_eq_right (by nlinarith)]; ring

section Reg

variable {K : Sides q} {r c : ℝ} (hK : IsReg K r c)
include hK

lemma fitReg_eq (hc : 0 ≤ c) (t θ : ℝ) :
    fittingRegion K t θ = {C | ∀ j, dot C (un q j) ≤ r * t - c * |θ|} := by
  ext C
  simp only [fittingRegion, mem_ofPred_eq, hK.u, hK.h, hK.a, hK.b, min_neg_c hc]
  refine forall_congr' fun j => ?_
  constructor <;> intro h <;> linarith

lemma sum_un (hc : 0 < c) : ∑ j, (un q j).1 = 0 ∧ ∑ j, (un q j).2 = 0 := by
  have h1 := K.sum_u1
  have h2 := K.sum_u2
  simp only [hK.u, hK.a, hK.b, sub_neg_eq_add, ← Finset.mul_sum] at h1 h2
  exact ⟨(mul_eq_zero.1 h1).resolve_left (by linarith),
    (mul_eq_zero.1 h2).resolve_left (by linarith)⟩

lemma polyReg_empty [NeZero q] (hc : 0 < c) {ρ : ℝ} (hρ : ρ < 0) :
    {C : ℝ × ℝ | ∀ j, dot C (un q j) ≤ ρ} = ∅ := by
  rw [eq_empty_iff_forall_notMem]
  intro C hC
  have hs : ∑ j : Fin q, dot C (un q j) = 0 := by
    simp only [dot, Finset.sum_add_distrib, ← Finset.mul_sum, (sum_un hK hc).1, (sum_un hK hc).2]
    ring
  have hlt : ∑ j : Fin q, dot C (un q j) < ∑ _j : Fin q, (0 : ℝ) :=
    Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty fun j _ => lt_of_le_of_lt (hC j) hρ
  simp at hlt
  linarith

omit hK in
lemma polyReg_smul {ρ : ℝ} (hρ : 0 < ρ) :
    {C : ℝ × ℝ | ∀ j, dot C (un q j) ≤ ρ} = ρ • Preg q := by
  ext C
  simp only [Preg]
  rw [mem_smul_set_iff_inv_smul_mem₀ hρ.ne']
  simp only [mem_ofPred_eq, dot_smul]
  refine forall_congr' fun j => ?_
  rw [inv_mul_le_iff₀ hρ, mul_one]

/-- The area of the fitting region, off the null set `ρ = 0`. -/
lemma volume_polyReg [NeZero q] (hq : 3 ≤ q) (hc : 0 < c) {ρ : ℝ} (hρ : ρ ≠ 0) :
    volume {C : ℝ × ℝ | ∀ j, dot C (un q j) ≤ ρ} =
      ENNReal.ofReal (q * tan (π / q) * max ρ 0 ^ 2) := by
  rcases lt_or_gt_of_ne hρ with h | h
  · rw [polyReg_empty hK hc h, measure_empty, max_eq_right h.le]; simp
  · rw [polyReg_smul h, Measure.volume_eq_prod, Measure.addHaar_smul, Module.finrank_prod,
      Module.finrank_self, ← Measure.volume_eq_prod, volume_Preg hq, max_eq_left h.le,
      abs_of_nonneg (by positivity), ← ENNReal.ofReal_mul (by positivity)]
    congr 1; ring

/-- **The spatial factor of the regular `q`-gon**: `q tan(π/q) r³ / (4c)`. -/
theorem spatial_reg [NeZero q] (hq : 3 ≤ q) (hr : 0 < r) (hc : 0 < c) :
    spatialVertexIntegral K = ENNReal.ofReal (q * tan (π / q) * r ^ 3 / (4 * c)) := by
  have hT : 0 ≤ q * tan (π / q) := by
    have := tanq_pos hq; have := q_pos hq; positivity
  unfold spatialVertexIntegral
  have hinner : ∀ θ : ℝ, ∫⁻ t in Ici (0 : ℝ),
      ENNReal.ofReal (exp (-2 * t)) * volume (fittingRegion K t θ)
      = ENNReal.ofReal (q * tan (π / q) * r ^ 2) *
          (ENNReal.ofReal (exp (-((2 * c / r) * |θ|))) * ENNReal.ofReal (1 / 4)) := by
    intro θ
    set a := c * |θ| / r
    have ha : 0 ≤ a := by positivity
    have hra : ∀ t, r * t - c * |θ| = r * (t - a) := fun t => by
      simp only [a]; field_simp
    calc ∫⁻ t in Ici (0 : ℝ), ENNReal.ofReal (exp (-2 * t)) * volume (fittingRegion K t θ)
        = ∫⁻ t, (Ici (0 : ℝ)).indicator (fun t => ENNReal.ofReal (exp (-2 * t)) *
            volume (fittingRegion K t θ)) t := (lintegral_indicator measurableSet_Ici _).symm
      _ = ∫⁻ t, (Ioi a).indicator (fun t => ENNReal.ofReal (q * tan (π / q) * r ^ 2) *
            ENNReal.ofReal (exp (-2 * t) * (t - a) ^ 2)) t := by
          refine lintegral_congr_ae ?_
          filter_upwards [Measure.ae_ne volume a] with t ht
          have hρ : r * t - c * |θ| ≠ 0 := by
            rw [hra]; exact mul_ne_zero hr.ne' (sub_ne_zero.2 ht)
          have hv := volume_polyReg hK hq hc hρ
          rw [← fitReg_eq hK hc.le, hra] at hv
          by_cases h : a < t
          · rw [indicator_of_mem (show t ∈ Ici (0 : ℝ) from ha.trans h.le),
              indicator_of_mem (show t ∈ Ioi a from h), hv, max_eq_left (by nlinarith),
              ← ENNReal.ofReal_mul (exp_pos _).le, ← ENNReal.ofReal_mul (by positivity)]
            congr 1; ring
          · rw [indicator_of_notMem (show t ∉ Ioi a from h)]
            by_cases h0 : t ∈ Ici (0 : ℝ)
            · rw [indicator_of_mem h0, hv, max_eq_right (by nlinarith [not_lt.1 h])]
              simp
            · rw [indicator_of_notMem h0]
      _ = _ := by
          rw [lintegral_indicator measurableSet_Ioi, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
            lintegral_inner_square]
          rw [show -(2 * a) = -((2 * c / r) * |θ|) by simp only [a]; ring]
  simp_rw [hinner]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_mul_const' _ _ ENNReal.ofReal_ne_top,
    lintegral_exp_neg_abs (by positivity), ← ENNReal.ofReal_mul (by positivity),
    ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  field_simp

/-! ### The cone factor -/

/-- A point on the vertical edge `j` of the prism `P_q × [-1, 1]`, at height `y`. -/
noncomputable def prismPt (q : ℕ) (j : Fin q) (y : ℝ) : R3 := ![(un q j).1, (un q j).2, y]

/-- Four prism points. -/
noncomputable def prismPts (q : ℕ) (k : Fin 4 → Fin q) (y : Fin 4 → ℝ) : Fin 4 → R3 :=
  fun i => prismPt q (k i) (y i)

lemma vertexMatrix_reg (k : Fin 4 → Fin q) (y : Fin 4 → ℝ) :
    vertexMatrix K (pointsOf k ((-c) • y) 0) =
      Matrix.of fun i j => ![r, 1, 1, c] j * homMat (prismPts q k y) i j := by
  ext i j
  fin_cases j <;>
    simp [vertexMatrix, row, pointsOf, homMat, prismPts, prismPt, hK.h, hK.u]

lemma det_reg (k : Fin 4 → Fin q) (y : Fin 4 → ℝ) :
    (vertexMatrix K (pointsOf k ((-c) • y) 0)).det = r * c * (homMat (prismPts q k y)).det := by
  rw [vertexMatrix_reg hK, Matrix.det_mul_row]
  simp [Fin.prod_univ_four]

lemma cone_reg_iff (hr : 0 < r) (hc : 0 < c) (k : Fin 4 → Fin q) (y : Fin 4 → ℝ) :
    vertexConeCondition K k ((-c) • y) ↔ PosBary (prismPts q k y) := by
  have hrow : ∀ (l : Fin 4 → ℝ) (j : Fin 4), ∑ i, l i * row K (pointsOf k ((-c) • y) 0 i) j =
      ![r * ∑ i, l i, ∑ i, l i * (un q (k i)).1, ∑ i, l i * (un q (k i)).2,
        c * ∑ i, l i * y i] j := by
    intro l j
    fin_cases j <;> simp [row, pointsOf, hK.h, hK.u, Finset.mul_sum] <;>
      refine Finset.sum_congr rfl fun i _ => by ring
  constructor
  · rintro ⟨l, hl, he⟩
    refine ⟨fun i => r * l i, fun i => mul_pos hr (hl i), ?_, ?_⟩
    · have := he 0; rw [hrow] at this; simpa [Finset.mul_sum] using this
    · have h1 := he 1; have h2 := he 2; have h3 := he 3
      rw [hrow] at h1 h2 h3
      simp at h1 h2 h3
      funext j
      fin_cases j
      · simp [prismPts, prismPt, Finset.sum_apply, ← Finset.mul_sum, h1]
        rw [show ∑ i, r * l i * (un q (k i)).1 = r * ∑ i, l i * (un q (k i)).1 by
          rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by ring, h1, mul_zero]
      · simp [prismPts, prismPt, Finset.sum_apply]
        rw [show ∑ i, r * l i * (un q (k i)).2 = r * ∑ i, l i * (un q (k i)).2 by
          rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by ring, h2, mul_zero]
      · simp [prismPts, prismPt, Finset.sum_apply]
        have : ∑ i, l i * y i = 0 := h3.resolve_left hc.ne'
        rw [show ∑ i, r * l i * y i = r * ∑ i, l i * y i by
          rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by ring, this, mul_zero]
  · rintro ⟨l, hl, h1, h0⟩
    have hj : ∀ j : Fin 3, ∑ i, l i * prismPts q k y i j = 0 := fun j => by
      have := congr_fun h0 j
      simpa [Finset.sum_apply] using this
    refine ⟨fun i => l i / r, fun i => div_pos (hl i) hr, fun j => ?_⟩
    rw [hrow]
    have e : ∀ f : Fin 4 → ℝ, ∑ i, l i / r * f i = (∑ i, l i * f i) / r := fun f => by
      rw [Finset.sum_div]; exact Finset.sum_congr rfl fun i _ => by ring
    fin_cases j
    · simp [← Finset.sum_div, h1]; field_simp
    · have := hj 0; simp [prismPts, prismPt] at this; simp [e, this]
    · have := hj 1; simp [prismPts, prismPt] at this; simp [e, this]
    · have := hj 2; simp [prismPts, prismPt] at this; simp [e, this]

/-- The cone-density integrand of the regular `q`-gon is `6 r c · Vol(T) 1{0 ∈ int T}`. -/
lemma cone_integrand_reg (hr : 0 < r) (hc : 0 < c) (k : Fin 4 → Fin q) (y : Fin 4 → ℝ) :
    ENNReal.ofReal ({s | vertexConeCondition K k s}.indicator
        (fun s => |(vertexMatrix K (pointsOf k s 0)).det|) ((-c) • y)) =
      ENNReal.ofReal (6 * r * c) * tetW (prismPts q k y) := by
  rw [tetW_eq, ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  by_cases h : PosBary (prismPts q k y)
  · rw [indicator_of_mem (show (-c) • y ∈ {s | vertexConeCondition K k s} from
      (cone_reg_iff hK hr hc k y).2 h),
      indicator_of_mem (show prismPts q k y ∈ {P : Fin 4 → R3 | PosBary P} from h),
      det_reg hK, abs_mul, abs_mul, abs_of_pos hr, abs_of_pos hc]
    ring
  · rw [indicator_of_notMem (show (-c) • y ∉ {s | vertexConeCondition K k s} from
      fun h' => h ((cone_reg_iff hK hr hc k y).1 h')),
      indicator_of_notMem (show prismPts q k y ∉ {P : Fin 4 → R3 | PosBary P} from h)]
    ring

end Reg

/-- Rescaling positions: `∫_{[-c,c]⁴} G = c⁴ ∫_{[-1,1]⁴} G(-c y) dy`. -/
lemma lintegral_box_scale {c : ℝ} (hc : 0 < c) (G : (Fin 4 → ℝ) → ℝ≥0∞) :
    ∫⁻ s, G s ∂(Measure.pi fun _ : Fin 4 => volume.restrict (Icc (-c) c)) =
      ENNReal.ofReal (c ^ 4) *
        ∫⁻ y, G ((-c) • y) ∂(Measure.pi fun _ : Fin 4 => volume.restrict (Icc (-1 : ℝ) 1)) := by
  have hbox : ∀ c : ℝ, (Measure.pi fun _ : Fin 4 => volume.restrict (Icc (-c) c))
      = (volume : Measure (Fin 4 → ℝ)).restrict (univ.pi fun _ => Icc (-c) c) := by
    intro c
    rw [volume_pi, Measure.restrict_pi_pi]
  have hc0 : (-c) ≠ 0 := by linarith
  set F : (Fin 4 → ℝ) → ℝ≥0∞ := (univ.pi fun _ => Icc (-c) c).indicator G
  have hpt : ∀ y : Fin 4 → ℝ, (univ.pi fun _ => Icc (-1 : ℝ) 1).indicator
      (fun y => G ((-c) • y)) y = F ((-c) • y) := by
    intro y
    have hiff : y ∈ univ.pi (fun _ => Icc (-1 : ℝ) 1) ↔
        (-c) • y ∈ univ.pi (fun _ => Icc (-c) c) := by
      simp only [mem_univ_pi, mem_Icc, Pi.smul_apply, smul_eq_mul]
      constructor
      · intro h i; constructor <;> nlinarith [(h i).1, (h i).2]
      · intro h i
        have h1 := (h i).1; have h2 := (h i).2
        constructor
        · by_contra hh; push Not at hh; nlinarith
        · by_contra hh; push Not at hh; nlinarith
    by_cases hy : y ∈ univ.pi (fun _ => Icc (-1 : ℝ) 1)
    · rw [indicator_of_mem hy]; simp only [F]; rw [indicator_of_mem (hiff.1 hy)]
    · rw [indicator_of_notMem hy]; simp only [F]
      rw [indicator_of_notMem (fun h => hy (hiff.2 h))]
  let e : (Fin 4 → ℝ) ≃ᵐ (Fin 4 → ℝ) := MeasurableEquiv.smul₀ (-c) hc0
  rw [hbox, hbox, ← lintegral_indicator (MeasurableSet.univ_pi fun _ => measurableSet_Icc),
    ← lintegral_indicator (MeasurableSet.univ_pi fun _ => measurableSet_Icc)]
  simp_rw [hpt]
  have hmap := Measure.map_addHaar_smul (volume : Measure (Fin 4 → ℝ)) hc0
  rw [show (fun y : Fin 4 → ℝ => F ((-c) • y)) = fun y => F (e y) from rfl,
    ← lintegral_map_equiv F e, show (⇑e : (Fin 4 → ℝ) → Fin 4 → ℝ) = ((-c) • ·) from rfl, hmap,
    lintegral_smul_measure, smul_eq_mul, Module.finrank_fin_fun, ← mul_assoc,
    ← ENNReal.ofReal_mul (by positivity),
    show c ^ 4 * |((-c) ^ 4)⁻¹| = 1 by
      rw [show (-c) ^ 4 = c ^ 4 by ring, abs_of_pos (by positivity)]; field_simp,
    ENNReal.ofReal_one, one_mul]

/-- The uniform distribution of a height on `[-1, 1]`. -/
noncomputable def unifH : Measure ℝ := (2 : ℝ≥0∞)⁻¹ • volume.restrict (Icc (-1 : ℝ) 1)

instance : IsProbabilityMeasure unifH := ⟨by
  rw [unifH, Measure.smul_apply, Measure.restrict_apply MeasurableSet.univ, univ_inter,
    Real.volume_Icc, smul_eq_mul]
  norm_num
  exact ENNReal.inv_mul_cancel (by norm_num) (by norm_num)⟩

/-- **`E[Vol(T) 1{0 ∈ int T}]`** for the tetrahedron `T` spanned by four independent points, each
on a uniformly chosen vertical edge of the prism `P_q × [-1, 1]` at a uniform height. -/
noncomputable def prismE (q : ℕ) : ℝ≥0∞ :=
  ∑ k : Fin 4 → Fin q, ((q : ℝ≥0∞)⁻¹) ^ 4 *
    ∫⁻ y, tetW (prismPts q k y) ∂(Measure.pi fun _ : Fin 4 => unifH)

lemma pi_unifH : (Measure.pi fun _ : Fin 4 => unifH) =
    ((2 : ℝ≥0∞)⁻¹) ^ 4 • Measure.pi fun _ : Fin 4 => volume.restrict (Icc (-1 : ℝ) 1) := by
  refine Measure.pi_eq fun s _ => ?_
  rw [Measure.smul_apply, Measure.pi_pi, smul_eq_mul]
  simp only [unifH, Measure.smul_apply, smul_eq_mul, Finset.prod_mul_distrib, Finset.prod_const,
    Finset.card_univ, Fintype.card_fin]

/-- The sum of the edge-choice integrals is `16 q⁴ E`. -/
lemma sum_tet_eq [NeZero q] :
    ∑ k : Fin 4 → Fin q, ∫⁻ y, tetW (prismPts q k y)
      ∂(Measure.pi fun _ : Fin 4 => volume.restrict (Icc (-1 : ℝ) 1)) =
      ENNReal.ofReal (16 * (q : ℝ) ^ 4) * prismE q := by
  rw [prismE, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  have hq : (q : ℝ≥0∞) ≠ 0 := by simp [NeZero.ne q]
  have : ENNReal.ofReal (16 * (q : ℝ) ^ 4) * ((q : ℝ≥0∞)⁻¹) ^ 4 * ((2 : ℝ≥0∞)⁻¹) ^ 4 = 1 := by
    rw [ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_pow (Nat.cast_nonneg q),
      ENNReal.ofReal_natCast, show ENNReal.ofReal 16 = 2 ^ 4 by norm_num,
      mul_assoc (2 ^ 4 : ℝ≥0∞), ← mul_pow, ENNReal.mul_inv_cancel hq (by simp), one_pow, mul_one,
      ← mul_pow, ENNReal.mul_inv_cancel (by norm_num) (by norm_num), one_pow]
  rw [pi_unifH, lintegral_smul_measure, smul_eq_mul, ← mul_assoc, ← mul_assoc, this, one_mul]

/-- **The cone factor of the regular `q`-gon**: `4 r c⁵ q⁴ E[Vol(T) 1{0 ∈ int T}]`. -/
theorem cone_reg [NeZero q] {K : Sides q} {r c : ℝ} (hK : IsReg K r c) (hr : 0 < r) (hc : 0 < c) :
    coneVertexDensity K = ENNReal.ofReal (4 * r * c ^ 5 * (q : ℝ) ^ 4) * prismE q := by
  unfold coneVertexDensity
  have hbox : ∀ k : Fin 4 → Fin q, (Measure.pi fun i => volume.restrict
      (Icc (K.a (k i)) (K.b (k i)))) = Measure.pi fun _ : Fin 4 => volume.restrict (Icc (-c) c) := by
    intro k; simp only [hK.a, hK.b]
  simp_rw [hbox]
  simp_rw [lintegral_box_scale hc, cone_integrand_reg hK hr hc]
  simp_rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  rw [← Finset.mul_sum, ← Finset.mul_sum, sum_tet_eq, ← mul_assoc, ← mul_assoc, ← mul_assoc]
  congr 1
  rw [show (1 / 24 : ℝ≥0∞) = ENNReal.ofReal (1 / 24) by
      rw [ENNReal.ofReal_div_of_pos (by norm_num)]; simp,
    ← ENNReal.ofReal_mul (by norm_num), ← ENNReal.ofReal_mul (by positivity),
    ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  ring

end Enclosing
