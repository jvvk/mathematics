import EnclosingCopy.Enclosing.VertexSpatial
import EnclosingCopy.Enclosing.Regular
import EnclosingCopy.Enclosing.SquareVertex
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral

/-!
# The square in the Poisson model: the vertex-candidate probability tends to `1/12`

The unit square (area one) has four sides with `h = 1/2`, normals `(±1, 0), (0, ±1)` and positions
`s ∈ [-1/2, 1/2]` (`squareSides`). `vertex_candidate_formula_limit` says that the probability of
a certified vertex candidate in the model truncated at depth `n` tends to
`spatialVertexIntegral · coneVertexDensity`. For the square:

* `spatial_square`: the fitting region at scale `t` and tilt `θ` is a square of side `t - |θ|`,
  so `spatialVertexIntegral = ∫∫_{t > |θ|} e^{-2t} (t - |θ|)² = 1/4`;
* `cone_square`: rescaling positions `s = σ/2` turns the cone density into `T_nd = 64/3` of
  `SquareVertex` (side `[-1, 1]`, `h = 1`) times `1/16 · 1/4`, so it is `1/3`;
* `square_vertex_candidate_limit`: the limit is `1/12`.

With the segment term `1/6` this is the vertex half of `p₄ = 1/4`.
-/

namespace Enclosing

open MeasureTheory Set Real ENNReal

/-- The unit square, as side data of a polygon of area one. -/
noncomputable def squareSides : Sides 4 where
  h := fun _ => 1 / 2
  u := ![(1, 0), (0, 1), (-1, 0), (0, -1)]
  a := fun _ => -1 / 2
  b := fun _ => 1 / 2
  hab := fun _ => by norm_num
  sum_u1 := by simp [Fin.sum_univ_four]
  sum_u2 := by simp [Fin.sum_univ_four]
  sum_h := by simp; norm_num
  sum_sq := by simp; norm_num

/-! ### The spatial factor -/

lemma fittingRegion_square {t θ : ℝ} (_ht : |θ| ≤ t) :
    fittingRegion squareSides t θ
      = Icc (-((t - |θ|) / 2)) ((t - |θ|) / 2) ×ˢ Icc (-((t - |θ|) / 2)) ((t - |θ|) / 2) := by
  have hm : min (θ * (-1 / 2)) (θ * (1 / 2)) = -|θ| / 2 := by
    rcases le_total 0 θ with h | h
    · rw [abs_of_nonneg h, min_eq_left (by linarith)]; ring
    · rw [abs_of_nonpos h, min_eq_right (by linarith)]; ring
  ext C
  simp only [fittingRegion, squareSides, Fin.forall_fin_succ, IsEmpty.forall_iff, mem_setOf_eq,
    mem_prod, mem_Icc, dot, hm]
  simp
  constructor
  · rintro ⟨h0, h1, h2, h3⟩
    refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;> linarith
  · rintro ⟨⟨h0, h1⟩, h2, h3⟩
    refine ⟨?_, ?_, ?_, ?_⟩ <;> linarith

lemma fittingRegion_square_empty {t θ : ℝ} (ht : t < |θ|) : fittingRegion squareSides t θ = ∅ := by
  have hm : min (θ * (-1 / 2)) (θ * (1 / 2)) = -|θ| / 2 := by
    rcases le_total 0 θ with h | h
    · rw [abs_of_nonneg h, min_eq_left (by linarith)]; ring
    · rw [abs_of_nonpos h, min_eq_right (by linarith)]; ring
  ext C
  simp only [fittingRegion, squareSides, Fin.forall_fin_succ, IsEmpty.forall_iff, mem_setOf_eq,
    dot, hm, mem_empty_iff_false, iff_false]
  simp
  intro h0 _ h2
  linarith

lemma volume_fittingRegion_square (t θ : ℝ) :
    volume (fittingRegion squareSides t θ) =
      (Ici |θ|).indicator (fun t => ENNReal.ofReal ((t - |θ|) ^ 2)) t := by
  by_cases ht : |θ| ≤ t
  · rw [indicator_of_mem (show t ∈ Ici |θ| from ht), fittingRegion_square ht,
      Measure.volume_eq_prod, Measure.prod_prod, Real.volume_Icc, ← ENNReal.ofReal_mul (by
        linarith)]
    congr 1; ring
  · rw [indicator_of_notMem (show t ∉ Ici |θ| from ht),
      fittingRegion_square_empty (lt_of_not_ge ht), measure_empty]

/-- `∫_{u > 0} u² e^{-2u} du = 1/4`, as a lower integral. -/
lemma lintegral_sq_exp :
    ∫⁻ u in Ioi (0 : ℝ), ENNReal.ofReal (u ^ 2 * Real.exp (-(2 * u))) = ENNReal.ofReal (1 / 4) := by
  have hg : IntegrableOn (fun u : ℝ => u ^ (2 : ℝ) * Real.exp (-2 * u ^ (1 : ℝ))) (Ioi 0) :=
    integrableOn_rpow_mul_exp_neg_mul_rpow (by norm_num) (by norm_num) (by norm_num)
  have hint : IntegrableOn (fun u : ℝ => u ^ 2 * Real.exp (-(2 * u))) (Ioi 0) := by
    refine hg.congr_fun (fun u hu => ?_) measurableSet_Ioi
    simp only [Real.rpow_one, neg_mul]
    rw [show u ^ (2 : ℝ) = u ^ 2 by exact_mod_cast Real.rpow_natCast u 2]
  rw [← ofReal_integral_eq_lintegral_ofReal hint
    ((ae_restrict_iff' measurableSet_Ioi).2 (Filter.Eventually.of_forall fun u _ => by positivity)),
    integral_pow_mul_exp_neg 2 (by norm_num : (0 : ℝ) < 2)]
  norm_num [Nat.factorial]

/-- `∫_{t > c} e^{-2t} (t - c)² dt = e^{-2c}/4`, as a lower integral. -/
lemma lintegral_inner_square (c : ℝ) :
    ∫⁻ t in Ioi c, ENNReal.ofReal (Real.exp (-2 * t) * (t - c) ^ 2)
      = ENNReal.ofReal (Real.exp (-(2 * c))) * ENNReal.ofReal (1 / 4) := by
  rw [← lintegral_sq_exp, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
    ← lintegral_indicator measurableSet_Ioi, ← lintegral_indicator measurableSet_Ioi,
    ← lintegral_add_right_eq_self _ c]
  refine lintegral_congr fun u => ?_
  by_cases hu : 0 < u
  · rw [indicator_of_mem (show u + c ∈ Ioi c by simp [hu]), indicator_of_mem (show u ∈ Ioi 0 from hu),
      ← ENNReal.ofReal_mul (Real.exp_pos _).le]
    congr 1
    rw [show -2 * (u + c) = -(2 * c) + -(2 * u) by ring, Real.exp_add]
    ring
  · rw [indicator_of_notMem (show u + c ∉ Ioi c by simpa using hu),
      indicator_of_notMem (show u ∉ Ioi (0 : ℝ) from hu)]

lemma integrable_exp_neg_two_abs : Integrable fun θ : ℝ => Real.exp (-(2 * |θ|)) := by
  rw [← integrableOn_univ, ← Iic_union_Ioi (a := (0 : ℝ))]
  refine IntegrableOn.union ?_ ?_
  · refine (integrableOn_exp_mul_Iic (a := 2) (by norm_num) 0).congr_fun (fun θ hθ => ?_)
      measurableSet_Iic
    rw [abs_of_nonpos (mem_Iic.1 hθ)]; ring_nf
  · refine (integrableOn_exp_mul_Ioi (a := -2) (by norm_num) 0).congr_fun (fun θ hθ => ?_)
      measurableSet_Ioi
    rw [abs_of_pos (mem_Ioi.1 hθ)]; ring_nf

/-- **The spatial factor of the square is `1/4`.** -/
theorem spatial_square : spatialVertexIntegral squareSides = ENNReal.ofReal (1 / 4) := by
  unfold spatialVertexIntegral
  have hinner : ∀ θ : ℝ, ∫⁻ t in Ici (0 : ℝ),
      ENNReal.ofReal (Real.exp (-2 * t)) * volume (fittingRegion squareSides t θ)
      = ENNReal.ofReal (Real.exp (-(2 * |θ|))) * ENNReal.ofReal (1 / 4) := by
    intro θ
    calc ∫⁻ t in Ici (0 : ℝ), ENNReal.ofReal (Real.exp (-2 * t)) * volume (fittingRegion squareSides t θ)
        = ∫⁻ t, (Ici (0 : ℝ)).indicator (fun t => ENNReal.ofReal (Real.exp (-2 * t)) *
            volume (fittingRegion squareSides t θ)) t := (lintegral_indicator measurableSet_Ici _).symm
      _ = ∫⁻ t, (Ioi |θ|).indicator
            (fun t => ENNReal.ofReal (Real.exp (-2 * t) * (t - |θ|) ^ 2)) t := by
          refine lintegral_congr_ae ?_
          filter_upwards [(Measure.ae_ne volume |θ|)] with t ht
          simp only [volume_fittingRegion_square]
          by_cases h : |θ| < t
          · rw [indicator_of_mem (show t ∈ Ici (0 : ℝ) from (abs_nonneg θ).trans h.le),
              indicator_of_mem (show t ∈ Ici |θ| from h.le),
              indicator_of_mem (show t ∈ Ioi |θ| from h), ← ENNReal.ofReal_mul (Real.exp_pos _).le]
          · have h' : t < |θ| := lt_of_le_of_ne (not_lt.1 h) ht
            rw [indicator_of_notMem (show t ∉ Ioi |θ| from fun h'' => h h'')]
            by_cases h0 : t ∈ Ici (0 : ℝ)
            · rw [indicator_of_mem h0, indicator_of_notMem (show t ∉ Ici |θ| from not_le.2 h'),
                mul_zero]
            · rw [indicator_of_notMem h0]
      _ = _ := by rw [lintegral_indicator measurableSet_Ioi, lintegral_inner_square]
  simp_rw [hinner]
  rw [lintegral_mul_const' _ _ ENNReal.ofReal_ne_top,
    ← ofReal_integral_eq_lintegral_ofReal integrable_exp_neg_two_abs
      (Filter.Eventually.of_forall fun θ => (Real.exp_pos _).le)]
  have := integral_exp_neg_abs (c := 2) (by norm_num)
  rw [this, ← ENNReal.ofReal_mul (by norm_num)]
  norm_num

/-! ### The cone factor -/

lemma squareSides_u (j : Fin 4) : squareSides.u j = un 4 j := by
  rw [un_four]; fin_cases j <;> simp [squareSides, ux, uy]

/-- The square's vertex matrix at positions `s` is `Amat` at `2s` with the first and last columns
halved. -/
lemma vertexMatrix_square (k : Fin 4 → Fin 4) (s : Fin 4 → ℝ) :
    vertexMatrix squareSides (pointsOf k s 0)
      = Amat k ((2 : ℝ) • s) * Matrix.diagonal ![1 / 2, 1, 1, 1 / 2] := by
  ext r c
  rw [Matrix.mul_diagonal]
  have hh : squareSides.h = fun _ => 1 / 2 := rfl
  fin_cases c <;> simp [vertexMatrix, row, pointsOf, Amat, squareSides_u, hh] <;> ring

lemma det_vertexMatrix_square (k : Fin 4 → Fin 4) (s : Fin 4 → ℝ) :
    (vertexMatrix squareSides (pointsOf k s 0)).det = (Amat k ((2 : ℝ) • s)).det / 4 := by
  rw [vertexMatrix_square, Matrix.det_mul, Matrix.det_diagonal]
  simp [Fin.prod_univ_four]
  ring

lemma cone_square_iff (k : Fin 4 → Fin 4) (s : Fin 4 → ℝ) :
    vertexConeCondition squareSides k s ↔ KKT k ((2 : ℝ) • s) := by
  have hrow : ∀ r c, row squareSides (pointsOf k s 0 r) c
      = Amat k ((2 : ℝ) • s) r c * ![1 / 2, 1, 1, 1 / 2] c := by
    intro r c
    have := congrFun (congrFun (vertexMatrix_square k s) r) c
    rw [Matrix.mul_diagonal] at this
    exact this
  unfold vertexConeCondition KKT
  set A := Amat k ((2 : ℝ) • s)
  set w : Fin 4 → ℝ := ![1 / 2, 1, 1, 1 / 2]
  -- a column sum of the square's rows is the `Amat` column sum times `w c`
  have hcol : ∀ (l : Fin 4 → ℝ) c,
      ∑ r, l r * row squareSides (pointsOf k s 0 r) c = (∑ r, l r * A r c) * w c := by
    intro l c; rw [Finset.sum_mul]; exact Finset.sum_congr rfl fun r _ => by rw [hrow]; ring
  have hscale : ∀ (l : Fin 4 → ℝ) (κ : ℝ) c, ∑ r, κ * l r * A r c = κ * ∑ r, l r * A r c := by
    intro l κ c; rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun r _ => by ring
  constructor
  · rintro ⟨l, hl, he⟩
    refine ⟨fun r => (1 / 2) * l r, fun r => by have := hl r; positivity, fun c => ?_⟩
    have h := he c
    rw [hcol] at h
    rw [hscale]
    fin_cases c <;> simp [w] at h ⊢ <;> linarith
  · rintro ⟨l, hl, he⟩
    refine ⟨fun r => 2 * l r, fun r => by have := hl r; positivity, fun c => ?_⟩
    have h := he c
    rw [hcol, hscale]
    fin_cases c <;> simp [w] at h ⊢ <;> linarith

/-- The cone-density integrand of the square, in terms of `SquareVertex.integrand`. -/
lemma cone_integrand_square (k : Fin 4 → Fin 4) (s : Fin 4 → ℝ) :
    ENNReal.ofReal ({s | vertexConeCondition squareSides k s}.indicator
        (fun s => |(vertexMatrix squareSides (pointsOf k s 0)).det|) s)
      = ENNReal.ofReal (integrand k ((2 : ℝ) • s)) / 4 := by
  unfold integrand
  by_cases h : vertexConeCondition squareSides k s
  · rw [indicator_of_mem (show s ∈ {s | vertexConeCondition squareSides k s} from h),
      indicator_of_mem (show (2 : ℝ) • s ∈ {σ | KKT k σ} from (cone_square_iff k s).1 h),
      det_vertexMatrix_square, abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 4),
      ENNReal.ofReal_div_of_pos (by norm_num)]
    norm_num
  · rw [indicator_of_notMem (show s ∉ {s | vertexConeCondition squareSides k s} from h),
      indicator_of_notMem (show (2 : ℝ) • s ∉ {σ | KKT k σ} from fun h' => h ((cone_square_iff k s).2 h'))]
    simp

/-- Rescaling positions: `∫_{[-1/2,1/2]⁴} G(2s) ds = (1/16) ∫_{[-1,1]⁴} G`. -/
lemma lintegral_half_box (G : (Fin 4 → ℝ) → ℝ≥0∞) :
    ∫⁻ s, G ((2 : ℝ) • s) ∂(Measure.pi fun _ : Fin 4 => volume.restrict (Icc (-1 / 2 : ℝ) (1 / 2)))
      = ENNReal.ofReal (1 / 16) * ∫⁻ σ, G σ ∂mu4 := by
  have hbox : ∀ c : ℝ, (Measure.pi fun _ : Fin 4 => volume.restrict (Icc (-c) c))
      = (volume : Measure (Fin 4 → ℝ)).restrict (univ.pi fun _ => Icc (-c) c) := by
    intro c
    rw [volume_pi, Measure.restrict_pi_pi]
  have h1 : (Measure.pi fun _ : Fin 4 => volume.restrict (Icc (-1 / 2 : ℝ) (1 / 2)))
      = (volume : Measure (Fin 4 → ℝ)).restrict (univ.pi fun _ => Icc (-(1 / 2)) (1 / 2)) := by
    rw [← hbox]; norm_num
  have h2 : mu4 = (volume : Measure (Fin 4 → ℝ)).restrict (univ.pi fun _ => Icc (-1) 1) := by
    rw [mu4, nu1, ← hbox]
  set F : (Fin 4 → ℝ) → ℝ≥0∞ := (univ.pi fun _ => Icc (-1 : ℝ) 1).indicator G
  have hpt : ∀ s : Fin 4 → ℝ, (univ.pi fun _ => Icc (-(1 / 2 : ℝ)) (1 / 2)).indicator
      (fun s => G ((2 : ℝ) • s)) s = F ((2 : ℝ) • s) := by
    intro s
    have hiff : s ∈ univ.pi (fun _ => Icc (-(1 / 2 : ℝ)) (1 / 2)) ↔
        (2 : ℝ) • s ∈ univ.pi (fun _ => Icc (-1 : ℝ) 1) := by
      simp only [mem_univ_pi, mem_Icc, Pi.smul_apply, smul_eq_mul]
      constructor
      · intro h i; constructor <;> linarith [(h i).1, (h i).2]
      · intro h i; constructor <;> linarith [(h i).1, (h i).2]
    by_cases hs : s ∈ univ.pi (fun _ => Icc (-(1 / 2 : ℝ)) (1 / 2))
    · rw [indicator_of_mem hs]; simp only [F]; rw [indicator_of_mem (hiff.1 hs)]
    · rw [indicator_of_notMem hs]; simp only [F]
      rw [indicator_of_notMem (fun h => hs (hiff.2 h))]
  let e : (Fin 4 → ℝ) ≃ᵐ (Fin 4 → ℝ) := MeasurableEquiv.smul₀ (2 : ℝ) two_ne_zero
  rw [h1, ← lintegral_indicator (MeasurableSet.univ_pi fun _ => measurableSet_Icc)]
  simp_rw [hpt]
  have hmap := Measure.map_addHaar_smul (volume : Measure (Fin 4 → ℝ)) (r := (2 : ℝ)) two_ne_zero
  rw [show (fun s : Fin 4 → ℝ => F ((2 : ℝ) • s)) = fun s => F (e s) from rfl,
    ← lintegral_map_equiv F e, show (⇑e : (Fin 4 → ℝ) → Fin 4 → ℝ) = ((2 : ℝ) • ·) from rfl, hmap,
    lintegral_smul_measure, h2, lintegral_indicator (MeasurableSet.univ_pi fun _ => measurableSet_Icc)]
  congr 1
  simp
  norm_num

lemma inv_four_eq : (4 : ℝ≥0∞)⁻¹ = ENNReal.ofReal (1 / 4) := by
  rw [ENNReal.ofReal_div_of_pos (by norm_num)]; simp

lemma inv_24_eq : (1 / 24 : ℝ≥0∞) = ENNReal.ofReal (1 / 24) := by
  rw [ENNReal.ofReal_div_of_pos (by norm_num)]; simp

lemma lintegral_integrand (k : Fin 4 → Fin 4) :
    ∫⁻ σ, ENNReal.ofReal (integrand k σ) ∂mu4
      = ENNReal.ofReal (if Function.Bijective k then 64 / 3 else 0) := by
  have hnn : ∀ σ, 0 ≤ integrand k σ := fun σ =>
    indicator_nonneg (fun _ _ => abs_nonneg _) _
  split_ifs with hb
  · rw [← integral_bij hb]
    exact (ofReal_integral_eq_lintegral_ofReal
      (Integrable.of_integral_ne_zero (by rw [integral_bij hb]; norm_num))
      (Filter.Eventually.of_forall hnn)).symm
  · simp [integrand_zero_of_not_bij hb]

/-- **The cone factor of the square is `1/3`.** -/
theorem cone_square : coneVertexDensity squareSides = ENNReal.ofReal (1 / 3) := by
  unfold coneVertexDensity
  have hterm : ∀ k : Fin 4 → Fin 4, ∫⁻ s, ENNReal.ofReal
      ({s | vertexConeCondition squareSides k s}.indicator
        (fun s => |(vertexMatrix squareSides (pointsOf k s 0)).det|) s)
      ∂(Measure.pi fun r => volume.restrict (Icc (squareSides.a (k r)) (squareSides.b (k r))))
      = ENNReal.ofReal (if Function.Bijective k then 1 / 3 else 0) := by
    intro k
    simp_rw [cone_integrand_square, ENNReal.div_eq_inv_mul]
    change ∫⁻ s, 4⁻¹ * ENNReal.ofReal (integrand k ((2 : ℝ) • s))
      ∂(Measure.pi fun _ : Fin 4 => volume.restrict (Icc (-1 / 2 : ℝ) (1 / 2))) = _
    rw [lintegral_const_mul' _ _ (by simp), lintegral_half_box (fun σ => ENNReal.ofReal (integrand k σ)),
      lintegral_integrand, inv_four_eq, ← ENNReal.ofReal_mul (by norm_num),
      ← ENNReal.ofReal_mul (by norm_num)]
    congr 1
    split_ifs <;> norm_num
  simp_rw [hterm]
  rw [← ENNReal.ofReal_sum_of_nonneg (fun k _ => by split_ifs <;> norm_num), Finset.sum_ite,
    Finset.sum_const_zero, add_zero, Finset.sum_const, card_bij, inv_24_eq,
    ← ENNReal.ofReal_mul (by norm_num)]
  norm_num

/-- **The square in the Poisson model.** The probability of a certified vertex candidate, in the
model truncated at depth `n`, tends to `1/12`: the vertex half of `p₄ = 1/4`. -/
theorem square_vertex_candidate_limit :
    Filter.Tendsto
      (fun n : ℕ => PoissonPP.law (Λ squareSides n) {ω | HasVertexCandidate squareSides n ω})
      Filter.atTop (nhds (ENNReal.ofReal (1 / 12))) := by
  have h := vertex_candidate_formula_limit squareSides
  rwa [spatial_square, cone_square, ← ENNReal.ofReal_mul (by norm_num),
    show (1 / 4 : ℝ) * (1 / 3) = 1 / 12 by norm_num] at h

end Enclosing
