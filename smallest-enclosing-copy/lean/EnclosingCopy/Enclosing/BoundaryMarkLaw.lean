import EnclosingCopy.Enclosing.SideMarkLaw
import EnclosingCopy.Enclosing.SideSeparation
import EnclosingCopy.Poisson.FiniteWindows

/-!
# Exact marked laws on the union of trimmed polygon side windows

The selector is measurable at every sample size, including zero. Once the trimmed
windows are disjoint and inside the polygon, the mapped restriction of the physical
uniform law is exactly `1/(n area)` times the fixed labelled strip intensity.
-/
namespace Enclosing
open MeasureTheory Set Filter Topology

variable {m : ℕ} [NeZero m]

/-- The physical observation window, the union of all trimmed side rectangles. -/
def boundaryWindow (K : Sides m) (a b : Fin m → ℝ) (T : ℝ) (n : ℕ) : Set (ℝ × ℝ) :=
  ⋃ i, sideWindow K i (a i) (b i) (T / n)

/-- Choose the first side window containing the point, then record position and scaled depth. -/
noncomputable def boundaryMark (K : Sides m) (a b : Fin m → ℝ) (T : ℝ) (n : ℕ) :
    (ℝ × ℝ) → Pt m :=
  PoissonPP.glueWindows (List.finRange m) (fun i => sideWindow K i (a i) (b i) (T / n))
    (fun i x => (i, sideMark K i n x)) (fun _ => (0, 0, 0))

omit [NeZero m] in
lemma measurableSet_boundaryWindow (K : Sides m) (a b : Fin m → ℝ) (T : ℝ) (n : ℕ) :
    MeasurableSet (boundaryWindow K a b T n) :=
  MeasurableSet.iUnion fun i => measurableSet_sideWindow K i (a i) (b i) _

lemma measurable_boundaryMark (K : Sides m) (a b : Fin m → ℝ) (T : ℝ) (n : ℕ) :
    Measurable (boundaryMark K a b T n) :=
  PoissonPP.measurable_glueWindows _ _ _ _
    (fun i => measurableSet_sideWindow K i (a i) (b i) _)
    (fun i => measurable_const.prodMk (measurable_sideMark K i n)) measurable_const

/-- The fixed labelled strip intensity with trimmed endpoints. -/
noncomputable def trimmedIntensity (a b : Fin m → ℝ) (T : ℝ) : Measure (Pt m) :=
  Measure.sum fun i => (Measure.dirac i).prod (volume.restrict (Icc (a i) (b i) ×ˢ Icc 0 T))

omit [NeZero m] in
lemma trimmedIntensity_mass (a b : Fin m → ℝ) (T : ℝ) :
    trimmedIntensity a b T univ = ∑ i, ENNReal.ofReal (b i - a i) * ENNReal.ofReal T := by
  rw [trimmedIntensity, Measure.sum_fintype, Measure.finsetSum_apply]
  apply Finset.sum_congr rfl
  intro i _
  rw [← univ_prod_univ, Measure.prod_prod, measure_univ, one_mul,
    Measure.restrict_apply_univ, rectangle_volume]

omit [NeZero m] in
instance trimmedIntensity_finite (a b : Fin m → ℝ) (T : ℝ) :
    IsFiniteMeasure (trimmedIntensity a b T) := by
  constructor
  rw [trimmedIntensity_mass]
  exact ENNReal.sum_lt_top.mpr fun i _ => by finiteness

lemma trimmedIntensity_mass_pos (a b : Fin m → ℝ) (hab : ∀ i, a i < b i) {T : ℝ}
    (hT : 0 < T) : 0 < trimmedIntensity a b T univ := by
  rw [trimmedIntensity_mass]
  have hp : 0 < ENNReal.ofReal (b 0 - a 0) * ENNReal.ofReal T := by
    exact bot_lt_iff_ne_bot.mpr
      (mul_ne_zero (ENNReal.ofReal_pos.mpr (sub_pos.mpr (hab 0))).ne'
        (ENNReal.ofReal_pos.mpr hT).ne')
  exact hp.trans_le (Finset.single_le_sum
    (f := fun i : Fin m => ENNReal.ofReal (b i - a i) * ENNReal.ofReal T)
    (fun i _ => bot_le) (Finset.mem_univ (0 : Fin m)))

variable {v : Fin m → ℝ × ℝ}

/-- Exact unnormalized marked restriction law for a contained disjoint family. -/
theorem mapped_boundaryWindow (hm : 3 ≤ m) (hv : ConvexPos v) (harea : area v = 1)
    (a b : Fin m → ℝ) (T : ℝ) (n : ℕ) (hn : 0 < n)
    (hsub : ∀ i, sideWindow (sidesOf v hm hv harea) i (a i) (b i) (T / n) ⊆
      polygonRegion (sidesOf v hm hv harea))
    (hdis : Pairwise (fun i j =>
      Disjoint (sideWindow (sidesOf v hm hv harea) i (a i) (b i) (T / n))
        (sideWindow (sidesOf v hm hv harea) j (a j) (b j) (T / n)))) :
    let K := sidesOf v hm hv harea
    Measure.map (boundaryMark K a b T n)
      ((polygonSample v hm hv harea).restrict (boundaryWindow K a b T n)) =
      ((volume (polygonRegion K))⁻¹ * ENNReal.ofReal (n : ℝ)⁻¹) • trimmedIntensity a b T := by
  intro K
  rw [boundaryWindow, boundaryMark,
    PoissonPP.map_glueWindows_union _ (fun i => List.mem_finRange i) _ _ _ _
      (fun i => measurableSet_sideWindow K i (a i) (b i) _)
      (fun i => measurable_const.prodMk (measurable_sideMark K i n)) measurable_const hdis]
  have he (i : Fin m) :
      Measure.map (fun x => (i, sideMark K i n x))
        ((polygonSample v hm hv harea).restrict (sideWindow K i (a i) (b i) (T / n))) =
      ((volume (polygonRegion K))⁻¹ * ENNReal.ofReal (n : ℝ)⁻¹) •
        (Measure.dirac i).prod (volume.restrict (Icc (a i) (b i) ×ˢ Icc 0 T)) := by
    rw [show (fun x => (i, sideMark K i n x)) = Prod.mk i ∘ sideMark K i n from rfl,
      ← Measure.map_map measurable_prodMk_left (measurable_sideMark K i n),
      mapped_polygon_sideWindow hm hv harea i (a i) (b i) T n hn (hsub i),
      Measure.map_smul _ measurable_prodMk_left.aemeasurable, Measure.dirac_prod]
  simp_rw [he]
  rw [trimmedIntensity, Measure.sum_fintype, Measure.sum_fintype, Finset.smul_sum]

/-- The exact marked restriction law holds for every sufficiently large sample size. -/
theorem mapped_boundaryWindow_eventually (hm : 3 ≤ m) (hv : ConvexPos v) (harea : area v = 1)
    (a b : Fin m → ℝ) (ha : ∀ i, aEnd v i < a i) (hab : ∀ i, a i ≤ b i)
    (hb : ∀ i, b i < bEnd v i) {T : ℝ} (hT : 0 ≤ T) :
    let K := sidesOf v hm hv harea
    ∀ᶠ n : ℕ in atTop, Measure.map (boundaryMark K a b T n)
      ((polygonSample v hm hv harea).restrict (boundaryWindow K a b T n)) =
      ((volume (polygonRegion K))⁻¹ * ENNReal.ofReal (n : ℝ)⁻¹) • trimmedIntensity a b T := by
  intro K
  filter_upwards [sideWindows_subset_eventually hm hv harea a b ha hab hb hT,
    sideWindows_disjoint_eventually hm hv harea a b ha hab hb hT,
    eventually_gt_atTop 0] with n hsub hdis hn
  exact mapped_boundaryWindow hm hv harea a b T n hn hsub hdis

/-- The conditional fixed mark law on the trimmed labelled strips. -/
noncomputable def boundaryMarkLaw (a b : Fin m → ℝ) (T : ℝ) : Measure (Pt m) :=
  ProbabilityTheory.cond (trimmedIntensity a b T) univ

lemma boundaryMarkLaw_probability (a b : Fin m → ℝ) (hab : ∀ i, a i < b i) {T : ℝ}
    (hT : 0 < T) : IsProbabilityMeasure (boundaryMarkLaw a b T) :=
  ProbabilityTheory.cond_isProbabilityMeasure (trimmedIntensity_mass_pos a b hab hT).ne'

/-- **The full trimmed boundary window has an eventually fixed conditional marked law.** -/
theorem boundaryMarkLaw_eventually (hm : 3 ≤ m) (hv : ConvexPos v) (harea : area v = 1)
    (a b : Fin m → ℝ) (ha : ∀ i, aEnd v i < a i) (hab : ∀ i, a i < b i)
    (hb : ∀ i, b i < bEnd v i) {T : ℝ} (hT : 0 < T) :
    let K := sidesOf v hm hv harea
    ∀ᶠ n : ℕ in atTop, Measure.map (boundaryMark K a b T n)
      (PoissonPP.windowLaw (polygonSample v hm hv harea) (boundaryWindow K a b T n)) =
        boundaryMarkLaw a b T := by
  intro K
  filter_upwards [mapped_boundaryWindow_eventually hm hv harea a b ha
    (fun i => (hab i).le) hb hT.le, eventually_gt_atTop 0] with n hmap hn
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hc : (volume (polygonRegion K))⁻¹ * ENNReal.ofReal (n : ℝ)⁻¹ ≠ 0 :=
    mul_ne_zero (ENNReal.inv_ne_zero.mpr
      (polygonRegion_volume_ne_top K (goodSides_of_convex hm hv harea)))
      (ENNReal.ofReal_pos.mpr (inv_pos.mpr hn')).ne'
  have hct : (volume (polygonRegion K))⁻¹ * ENNReal.ofReal (n : ℝ)⁻¹ ≠ ⊤ :=
    ENNReal.mul_ne_top (ENNReal.inv_ne_top.mpr (polygonRegion_volume_pos hm hv harea).ne')
      ENNReal.ofReal_ne_top
  have he := PoissonPP.mapped_windowLaw (polygonSample v hm hv harea)
    (boundaryWindow K a b T n) (boundaryMark K a b T n) (measurable_boundaryMark K a b T n)
    (trimmedIntensity a b T) (trimmedIntensity_mass_pos a b hab hT).ne' _ hc hct hmap
  simpa only [boundaryMarkLaw, ProbabilityTheory.cond, Measure.restrict_univ] using he

end Enclosing
