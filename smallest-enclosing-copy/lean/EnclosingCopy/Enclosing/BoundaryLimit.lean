import EnclosingCopy.Enclosing.BoundaryMarkLaw
import EnclosingCopy.Poisson.WindowMeasurability

/-!
# A marked Poisson limit for actual polygon samples in trimmed boundary windows

For every fixed cutoff and fixed positive endpoint margins, the spatial mark law
is eventually exact. Thus the only event-convergence hypothesis is almost-sure
stabilization at each finite count. The limiting intensity is planar strip area
divided by the actual physical polygon area. Optimum stability is in `Theorem1Events`.
-/
namespace Enclosing
open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal
variable {m : ℕ} [NeZero m] {v : Fin m → ℝ × ℝ}

/-- The rare-window count rate is eventually exactly its fixed strip area divided by area. -/
theorem boundaryWindow_scaled_mass (hm : 3 ≤ m) (hv : ConvexPos v) (harea : area v = 1)
    (a b : Fin m → ℝ) (ha : ∀ i, aEnd v i < a i) (hab : ∀ i, a i ≤ b i)
    (hb : ∀ i, b i < bEnd v i) {T : ℝ} (hT : 0 ≤ T) :
    let K := sidesOf v hm hv harea
    ∀ᶠ n : ℕ in atTop, (n : ℝ) * (polygonSample v hm hv harea).real
      (boundaryWindow K a b T n) = (trimmedIntensity a b T).real univ /
        (volume (polygonRegion K)).toReal := by
  intro K
  filter_upwards [mapped_boundaryWindow_eventually hm hv harea a b ha hab hb hT,
    eventually_gt_atTop 0] with n hmap hn
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hmass := PoissonPP.mapped_window_mass (polygonSample v hm hv harea)
    (boundaryWindow K a b T n) (boundaryMark K a b T n) (measurable_boundaryMark K a b T n)
    (trimmedIntensity a b T) _ hmap
  rw [measureReal_def, hmass, ENNReal.toReal_mul, ENNReal.toReal_mul,
    ENNReal.toReal_inv, ENNReal.toReal_ofReal (inv_nonneg.mpr hn'.le), measureReal_def]
  dsimp only [K]
  field_simp

/-- Normalize the count rate and fixed conditional law back to the geometric intensity. -/
lemma boundary_intensity_normalization (hm : 3 ≤ m) (hv : ConvexPos v) (harea : area v = 1)
    (a b : Fin m → ℝ) (hab : ∀ i, a i < b i) {T : ℝ} (hT : 0 < T) :
    let K := sidesOf v hm hv harea
    let A := (volume (polygonRegion K)).toReal
    ENNReal.ofReal ((trimmedIntensity a b T).real univ / A) • boundaryMarkLaw a b T =
      ENNReal.ofReal A⁻¹ • trimmedIntensity a b T := by
  intro K A
  rw [boundaryMarkLaw, ProbabilityTheory.cond, Measure.restrict_univ, smul_smul]
  have he : ENNReal.ofReal ((trimmedIntensity a b T).real univ / A) =
      trimmedIntensity a b T univ * ENNReal.ofReal A⁻¹ := by
    rw [div_eq_mul_inv, ENNReal.ofReal_mul measureReal_nonneg, measureReal_def,
      ENNReal.ofReal_toReal (measure_ne_top _ _)]
  rw [he, mul_right_comm,
    ENNReal.mul_inv_cancel (trimmedIntensity_mass_pos a b hab hT).ne' (measure_ne_top _ _),
    one_mul]

/-- **Actual iid polygon samples have the trimmed marked boundary Poisson limit.**
Spatial mark convergence is proved here. Almost-sure finite-count event stabilization
is the explicit input `hstable` (for the enclosing-copy event see `Theorem1Events`). -/
theorem polygon_trimmed_window_limit (hm : 3 ≤ m) (hv : ConvexPos v) (harea : area v = 1)
    (a b : Fin m → ℝ) (ha : ∀ i, aEnd v i < a i) (hab : ∀ i, a i < b i)
    (hb : ∀ i, b i < bEnd v i) {T : ℝ} (hT : 0 < T)
    (E : ℕ → Multiset (Pt m) → Prop) (F : Multiset (Pt m) → Prop)
    (hE : ∀ n k, MeasurableSet {x : Fin k → Pt m | E n (PoissonPP.config x)})
    (hF : ∀ k, MeasurableSet {x : Fin k → Pt m | F (PoissonPP.config x)})
    (hstable : ∀ k, ∀ᵐ x : Fin k → Pt m ∂(Measure.pi fun _ => boundaryMarkLaw a b T),
      ∀ᶠ n in atTop, E n (PoissonPP.config x) ↔ F (PoissonPP.config x)) :
    let K := sidesOf v hm hv harea
    let A := (volume (polygonRegion K)).toReal
    Tendsto (fun n : ℕ => (Measure.pi fun _ : Fin n => polygonSample v hm hv harea).real
      {x | E n ((PoissonPP.inWindow (boundaryWindow K a b T n) (PoissonPP.config x)).map
        (boundaryMark K a b T n))}) atTop
      (𝓝 ((PoissonPP.law (ENNReal.ofReal A⁻¹ • trimmedIntensity a b T)).real
        {ω | F (PoissonPP.config ω.2)})) := by
  intro K A
  let _ := boundaryMarkLaw_probability a b hab hT
  let r : ℝ≥0 := ⟨(trimmedIntensity a b T).real univ / A,
    div_nonneg measureReal_nonneg (physical_area_pos hm hv harea).le⟩
  have he : (fun n : ℕ => (n : ℝ) * (polygonSample v hm hv harea).real
      (boundaryWindow K a b T n)) =ᶠ[atTop] (fun _ => (r : ℝ)) :=
    boundaryWindow_scaled_mass hm hv harea a b ha (fun i => (hab i).le) hb hT.le
  have hr : Tendsto (fun n : ℕ => (n : ℝ) * (polygonSample v hm hv harea).real
      (boundaryWindow K a b T n)) atTop (𝓝 (r : ℝ)) := tendsto_const_nhds.congr' he.symm
  have hEB (n k : ℕ) : MeasurableSet {x : Fin k → ℝ × ℝ |
      E n ((PoissonPP.inWindow (boundaryWindow K a b T n) (PoissonPP.config x)).map
        (boundaryMark K a b T n))} :=
    PoissonPP.measurableSet_window_event (measurableSet_boundaryWindow K a b T n)
      (boundaryMark K a b T n) (measurable_boundaryMark K a b T n) (E n) (hE n)
  have ht := PoissonPP.iid_fixed_mark_window_limit (fun _ => polygonSample v hm hv harea)
    (boundaryMarkLaw a b T) (boundaryWindow K a b T) (measurableSet_boundaryWindow K a b T)
    (boundaryMark K a b T) (measurable_boundaryMark K a b T) E F hE hF hEB hr
    (boundaryMarkLaw_eventually hm hv harea a b ha hab hb hT) hstable
  have hnorm : (r : ℝ≥0∞) • boundaryMarkLaw a b T =
      ENNReal.ofReal A⁻¹ • trimmedIntensity a b T := by
    rw [← ENNReal.ofReal_coe_nnreal]
    change ENNReal.ofReal ((trimmedIntensity a b T).real univ / A) •
      (boundaryMarkLaw a b T : Measure (Pt m)) = _
    exact boundary_intensity_normalization hm hv harea a b hab hT
  rwa [hnorm] at ht

/-- **The trimmed boundary point process converges on every measurable configuration event.** -/
theorem polygon_trimmed_event_limit (hm : 3 ≤ m) (hv : ConvexPos v) (harea : area v = 1)
    (a b : Fin m → ℝ) (ha : ∀ i, aEnd v i < a i) (hab : ∀ i, a i < b i)
    (hb : ∀ i, b i < bEnd v i) {T : ℝ} (hT : 0 < T) (F : Multiset (Pt m) → Prop)
    (hF : ∀ k, MeasurableSet {x : Fin k → Pt m | F (PoissonPP.config x)}) :
    let K := sidesOf v hm hv harea
    let A := (volume (polygonRegion K)).toReal
    Tendsto (fun n : ℕ => (Measure.pi fun _ : Fin n => polygonSample v hm hv harea).real
      {x | F ((PoissonPP.inWindow (boundaryWindow K a b T n) (PoissonPP.config x)).map
        (boundaryMark K a b T n))}) atTop
      (𝓝 ((PoissonPP.law (ENNReal.ofReal A⁻¹ • trimmedIntensity a b T)).real
        {ω | F (PoissonPP.config ω.2)})) := by
  apply polygon_trimmed_window_limit hm hv harea a b ha hab hb hT (fun _ => F) F
    (fun _ => hF) hF
  intro k
  exact Eventually.of_forall fun _ => Eventually.of_forall fun _ => Iff.rfl

end Enclosing
