import EnclosingCopy.Enclosing.TangentFit
import EnclosingCopy.Enclosing.TangentObjective

/-!
# Fitting-event stability on a compact optimal face

The hypotheses are deterministic and explicit: the optimal face is compact, the
LP objective controls tilt gaps, and a fitting optimum has a strictly fitting
representative. Almost-sure verification is in `Theorem1Events` and `Theorem1Strict`.
-/
namespace Enclosing
open Set Filter Topology
variable {m : ℕ} (K : Sides m)

lemma continuous_tangentFitSlack (i : Fin m) (s : ℝ) :
    Continuous (fun p : ℝ × Copy => tangentFitSlack K p.1 p.2 i s) := by
  unfold tangentFitSlack Hs dot sideTangent; fun_prop

/-- Strictly fitting copies keep fitting under the finite correction. -/
lemma tangentFits_eventually_of_strict (z : Copy)
    (hz : ∀ i, Hs K z i < min (z.2.2 * K.a i) (z.2.2 * K.b i)) :
    ∀ᶠ q : ℝ in 𝓝 0, TangentFits K q z := by
  apply eventually_all.mpr
  intro i
  have ha : 0 < tangentFitSlack K 0 z i (K.a i) := by
    simp only [tangentFitSlack, zero_mul, add_zero]
    linarith [lt_of_lt_of_le (hz i) (min_le_left _ _)]
  have hb : 0 < tangentFitSlack K 0 z i (K.b i) := by
    simp only [tangentFitSlack, zero_mul, add_zero]
    linarith [lt_of_lt_of_le (hz i) (min_le_right _ _)]
  have hca : Continuous (fun q => tangentFitSlack K q z i (K.a i)) := by
    unfold tangentFitSlack; fun_prop
  have hcb : Continuous (fun q => tangentFitSlack K q z i (K.b i)) := by
    unfold tangentFitSlack; fun_prop
  exact ((hca.tendsto 0).eventually (Ioi_mem_nhds ha)).and
    ((hcb.tendsto 0).eventually (Ioi_mem_nhds hb)) |>.mono fun _ h => ⟨h.1.le, h.2.le⟩

/-- If no point of a compact face fits, the finite correction cannot create a
fitting point on that face once the inverse sample size is sufficiently small. -/
lemma tangentFits_eventually_none (S : Set Copy) (hS : IsCompact S)
    (hfit : ∀ z ∈ S, ¬ Fits K z) :
    ∀ᶠ q : ℝ in 𝓝 0, ∀ z ∈ S, ¬ TangentFits K q z := by
  apply hS.eventually_forall_of_forall_eventually
  intro z hz
  have hf := hfit z hz
  simp only [Fits, not_forall, not_le] at hf
  obtain ⟨i, hi⟩ := hf
  rcases le_total (z.2.2 * K.a i) (z.2.2 * K.b i) with h | h
  · rw [min_eq_left h] at hi
    have hzero : tangentFitSlack K 0 z i (K.a i) < 0 := by
      simp only [tangentFitSlack, zero_mul, add_zero]; linarith
    have he := ((continuous_tangentFitSlack K i (K.a i)).tendsto (0, z)).eventually
      (Iio_mem_nhds hzero)
    exact he.mono fun p hp hcopy => (not_le_of_gt hp) (hcopy i).1
  · rw [min_eq_right h] at hi
    have hzero : tangentFitSlack K 0 z i (K.b i) < 0 := by
      simp only [tangentFitSlack, zero_mul, add_zero]; linarith
    have he := ((continuous_tangentFitSlack K i (K.b i)).tendsto (0, z)).eventually
      (Iio_mem_nhds hzero)
    exact he.mono fun p hp hcopy => (not_le_of_gt hp) (hcopy i).2

/-- Compact-face fitting is stable when its maximum fit margin is nonzero,
expressed by existence of a strict representative whenever a fit exists. -/
theorem tangent_fit_compact_stability (S : Set Copy) (hS : IsCompact S)
    (hstrict : (∃ z ∈ S, Fits K z) →
      ∃ z ∈ S, ∀ i, Hs K z i < min (z.2.2 * K.a i) (z.2.2 * K.b i)) :
    ∀ᶠ q : ℝ in 𝓝 0,
      (∃ z ∈ S, TangentFits K q z) ↔ ∃ z ∈ S, Fits K z := by
  classical
  by_cases hf : ∃ z ∈ S, Fits K z
  · obtain ⟨z, hz, hsz⟩ := hstrict hf
    exact (tangentFits_eventually_of_strict K z hsz).mono fun q hq =>
      ⟨fun _ => hf, fun _ => ⟨z, hz, hq⟩⟩
  · have hnone : ∀ z ∈ S, ¬ Fits K z := by
      intro z hz hfit; exact hf ⟨z, hz, hfit⟩
    exact (tangentFits_eventually_none K S hS hnone).mono fun q hq =>
      ⟨fun ⟨z, hz, hfit⟩ => False.elim (hq z hz hfit), fun h => False.elim (hf h)⟩

/-- The entire optimal face, rather than a chosen optimizer, decides the fitting event.
This applies equally to a certified vertex and a parallel-side segment, once
localization, compactness and the strict fit margin have been supplied. -/
theorem tangent_enclosing_event_stability (G : Set Copy) (zs : Copy) (hzs : zs ∈ G)
    {R D : ℝ} (hR : 0 ≤ R) (hD : 0 ≤ D) (ht : ∀ z ∈ G, |z.2.2| ≤ R)
    (hopt : ∀ z ∈ G, zs.1 ≤ z.1)
    (hgap : ∀ z ∈ G, |z.2.2 - zs.2.2| ≤ D * (z.1 - zs.1))
    (hS : IsCompact {z ∈ G | z.1 = zs.1})
    (hstrict : (∃ z ∈ G, z.1 = zs.1 ∧ Fits K z) →
      ∃ z ∈ G, z.1 = zs.1 ∧
        ∀ i, Hs K z i < min (z.2.2 * K.a i) (z.2.2 * K.b i)) :
    ∀ᶠ n : ℕ in atTop,
      (∃ z ∈ G, TangentFits K (1 / n) z ∧
        ∀ y ∈ G, tangentScale (1 / n) z ≤ tangentScale (1 / n) y) ↔
      ∃ z ∈ G, z.1 = zs.1 ∧ Fits K z := by
  have hf := tangentScale_optimal_face hR hD G zs hzs (ht zs hzs) hopt hgap
  have he := tangent_fit_compact_stability K {z ∈ G | z.1 = zs.1} hS
    (by simpa only [mem_ofPred_eq, exists_and_left, and_assoc] using hstrict)
  have hq : Tendsto (fun n : ℕ => (1 : ℝ) / n) atTop (𝓝 0) :=
    tendsto_const_div_atTop_nhds_zero_nat 1
  filter_upwards [hf, hq.eventually he] with n hn hen
  constructor
  · rintro ⟨z, hz, hfit, hmin⟩
    have hz0 := (hn z hz (ht z hz)).mp (hmin zs hzs)
    obtain ⟨y, ⟨hy, hy0⟩, hfy⟩ := hen.mp ⟨z, ⟨hz, hz0⟩, hfit⟩
    exact ⟨y, hy, hy0, hfy⟩
  · rintro ⟨z, hz, hz0, hfit⟩
    obtain ⟨y, ⟨hy, hy0⟩, hfy⟩ := hen.mpr ⟨z, ⟨hz, hz0⟩, hfit⟩
    refine ⟨y, hy, hfy, ?_⟩
    have hyScale := tangentScale_eq_of_objective_eq y zs hy0 (hgap y hy) (1 / n)
    intro w hw
    rw [hyScale]
    by_contra h
    have hwle : tangentScale (1 / n) w ≤ tangentScale (1 / n) zs := (not_le.mp h).le
    have hw0 := (hn w hw (ht w hw)).mp hwle
    have hwScale := tangentScale_eq_of_objective_eq w zs hw0 (hgap w hw) (1 / n)
    rw [hwScale] at h
    exact h le_rfl

end Enclosing
