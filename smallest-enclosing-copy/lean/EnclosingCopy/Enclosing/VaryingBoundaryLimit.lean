import EnclosingCopy.Enclosing.UniformBoundary
import EnclosingCopy.Poisson.EventConvergence

/-!
# Varying configuration events in the full physical boundary window

Uniform event comparison transfers any almost-sure stabilized Poisson event to
actual iid samples. The stability premise is explicit; for the enclosing-copy event it is
`poisson_stable` (Theorem1Events).
-/
namespace Enclosing
open MeasureTheory Set Filter Topology
variable {m : ℕ} [NeZero m] {v : Fin m → ℝ × ℝ}

/-- Full-window varying-event limit for actual uniform polygon samples. -/
theorem polygon_boundary_varying_event_limit (hm : 3 ≤ m) (hv : ConvexPos v)
    (harea : area v = 1) {T : ℝ} (hT : 0 < T)
    (E : ℕ → Multiset (Pt m) → Prop) (F : Multiset (Pt m) → Prop)
    (hE : ∀ n k, MeasurableSet {x : Fin k → Pt m | E n (PoissonPP.config x)})
    (hF : ∀ k, MeasurableSet {x : Fin k → Pt m | F (PoissonPP.config x)})
    (hstable : ∀ᵐ ω ∂PoissonPP.law (Λ (sidesOf v hm hv harea) T),
      ∀ᶠ n in atTop, E n (PoissonPP.config ω.2) ↔ F (PoissonPP.config ω.2)) :
    let K := sidesOf v hm hv harea
    Tendsto (fun n : ℕ => (Measure.pi fun _ : Fin n => polygonSample v hm hv harea).real
      {x | E n ((PoissonPP.inWindow (physicalBoundaryWindow K T n)
        (PoissonPP.config x)).map (physicalBoundaryMark K T n))}) atTop
      (𝓝 ((PoissonPP.law (Λ K T)).real {ω | F (PoissonPP.config ω.2)})) := by
  intro K
  let p := fun n : ℕ => (Measure.pi fun _ : Fin n => polygonSample v hm hv harea).real
    {x | E n ((PoissonPP.inWindow (physicalBoundaryWindow K T n)
      (PoissonPP.config x)).map (physicalBoundaryMark K T n))}
  let q := fun n : ℕ => (PoissonPP.law (Λ K T)).real {ω | E n (PoissonPP.config ω.2)}
  have hq : Tendsto q atTop
      (𝓝 ((PoissonPP.law (Λ K T)).real {ω | F (PoissonPP.config ω.2)})) :=
    PoissonPP.event_probability_limit_of_ae _ (fun n (ω : PoissonPP.Sample (Pt m)) => E n (PoissonPP.config ω.2))
      (fun (ω : PoissonPP.Sample (Pt m)) => F (PoissonPP.config ω.2))
      (fun n => PoissonPP.measurableSet_sample (fun k => by exact hE n k))
      (PoissonPP.measurableSet_sample (fun k => by exact hF k)) hstable
  have hd : Tendsto (fun n => p n - q n) atTop (𝓝 0) := by
    apply Metric.tendsto_atTop.mpr
    intro ε hε
    have he := polygon_boundary_uniform_error hm hv harea hT ε hε
    have he' : ∀ᶠ n : ℕ in atTop, dist (p n - q n) 0 < ε := by
      filter_upwards [he] with n hn
      simpa only [Real.dist_eq, sub_zero] using hn (E n) (hE n)
    exact eventually_atTop.mp he'
  simpa only [sub_add_cancel, zero_add] using hd.add hq

end Enclosing
