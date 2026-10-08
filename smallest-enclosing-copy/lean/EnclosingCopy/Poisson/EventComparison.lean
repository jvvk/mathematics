import EnclosingCopy.Poisson.IIDBounds

/-!
# Comparing events outside a rare exceptional set

Agreement away from an exceptional set controls every event probability, without
any continuity requirement on the event. The iid union bound is stated in real
probabilities for use with geometric area estimates.
-/
namespace PoissonPP
open MeasureTheory Set
variable {α : Type*} [MeasurableSpace α]

theorem event_probability_diff_le (μ : Measure α) [IsProbabilityMeasure μ]
    {E F B : Set α} (hagrees : ∀ x ∉ B, x ∈ E ↔ x ∈ F) :
    |μ.real E - μ.real F| ≤ μ.real B := by
  have hEF : E ⊆ F ∪ B := by
    intro x hx
    by_cases hB : x ∈ B
    · exact Or.inr hB
    · exact Or.inl ((hagrees x hB).mp hx)
  have hFE : F ⊆ E ∪ B := by
    intro x hx
    by_cases hB : x ∈ B
    · exact Or.inr hB
    · exact Or.inl ((hagrees x hB).mpr hx)
  have h₁ := (measureReal_mono (μ := μ) hEF (measure_ne_top μ _)).trans (measureReal_union_le F B)
  have h₂ := (measureReal_mono (μ := μ) hFE (measure_ne_top μ _)).trans (measureReal_union_le E B)
  exact abs_le.mpr ⟨by linarith, by linarith⟩

theorem iid_hit_real_le (μ : Measure α) [IsProbabilityMeasure μ] {B : Set α}
    (hB : MeasurableSet B) (n : ℕ) :
    (Measure.pi fun _ : Fin n => μ).real {x | ∃ i, x i ∈ B} ≤ (n : ℝ) * μ.real B := by
  have hle := ENNReal.toReal_mono (by finiteness) (iid_hit_le μ hB n)
  simpa only [ENNReal.toReal_mul, ENNReal.toReal_natCast, measureReal_def] using hle

end PoissonPP
