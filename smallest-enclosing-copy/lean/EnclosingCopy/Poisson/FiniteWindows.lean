import EnclosingCopy.Poisson.ConditionalWindow

/-!
# Measurable marking of disjoint finite windows

A finite list of observation windows selects the first matching local mark, with a
fixed fallback outside the union. The map is measurable even when windows overlap.
For disjoint windows its restricted pushforward is the sum of the local pushforwards.
-/
namespace PoissonPP
open MeasureTheory Set
variable {ι α β : Type*} [MeasurableSpace α] [MeasurableSpace β]

/-- Glue local mark maps in list order, using a fallback outside their windows. -/
noncomputable def glueWindows (l : List ι) (B : ι → Set α) (f : ι → α → β)
    (fallback : α → β) : α → β := by
  classical
  exact l.foldr (fun i g => (B i).piecewise (f i) g) fallback

lemma measurable_glueWindows (l : List ι) (B : ι → Set α) (f : ι → α → β)
    (fallback : α → β) (hB : ∀ i, MeasurableSet (B i)) (hf : ∀ i, Measurable (f i))
    (hfall : Measurable fallback) : Measurable (glueWindows l B f fallback) := by
  classical
  induction l with
  | nil => exact hfall
  | cons i l ih => exact (hf i).piecewise (hB i) ih

omit [MeasurableSpace α] [MeasurableSpace β] in
lemma glueWindows_eq (l : List ι) (B : ι → Set α) (f : ι → α → β)
    (fallback : α → β) (i : ι) (hi : i ∈ l) {x : α} (hx : x ∈ B i)
    (hother : ∀ j ∈ l, j ≠ i → x ∉ B j) : glueWindows l B f fallback x = f i x := by
  classical
  induction l with
  | nil => simp at hi
  | cons j l ih =>
    by_cases hji : j = i
    · subst j; simp [glueWindows, hx]
    · have hjx : x ∉ B j := hother j (by simp) hji
      have hil : i ∈ l := by simpa [hji, Ne.symm hji] using hi
      simpa [glueWindows, hjx] using ih hil (fun k hk => hother k (by simp [hk]))

/-- The glued marker agrees almost everywhere with each local marker on its window. -/
lemma map_glueWindows_restrict (l : List ι) (hl : ∀ i, i ∈ l)
    (μ : Measure α) (B : ι → Set α) (f : ι → α → β) (fallback : α → β)
    (hB : ∀ i, MeasurableSet (B i)) (hdis : Pairwise (fun i j => Disjoint (B i) (B j))) (i : ι) :
    Measure.map (glueWindows l B f fallback) (μ.restrict (B i)) =
      Measure.map (f i) (μ.restrict (B i)) := by
  apply Measure.map_congr
  filter_upwards [ae_restrict_mem (hB i)] with x hx
  apply glueWindows_eq l B f fallback i (hl i) hx
  intro j _ hji hjx
  exact Set.disjoint_left.mp (hdis hji) hjx hx

/-- A disjoint finite union maps to the sum of its local window laws. -/
theorem map_glueWindows_union [Countable ι] (l : List ι) (hl : ∀ i, i ∈ l)
    (μ : Measure α) (B : ι → Set α) (f : ι → α → β) (fallback : α → β)
    (hB : ∀ i, MeasurableSet (B i)) (hf : ∀ i, Measurable (f i))
    (hfall : Measurable fallback) (hdis : Pairwise (fun i j => Disjoint (B i) (B j))) :
    Measure.map (glueWindows l B f fallback) (μ.restrict (⋃ i, B i)) =
      Measure.sum fun i => Measure.map (f i) (μ.restrict (B i)) := by
  rw [Measure.restrict_iUnion hdis hB,
    Measure.map_sum (measurable_glueWindows l B f fallback hB hf hfall).aemeasurable]
  congr 1
  funext i
  exact map_glueWindows_restrict l hl μ B f fallback hB hdis i

end PoissonPP
