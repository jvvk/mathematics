import EnclosingCopy.Poisson.ConditionalWindow
import Mathlib.Data.List.OfFn

/-!
# Measurability of filtered and marked configuration events

Measurability at every fixed tuple size implies measurability after retaining points
in a measurable window and applying a measurable mark map. The proof splits the
finite sample by its exact retained index set, then enumerates that fixed subset.
-/
namespace PoissonPP
open MeasureTheory Set
variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]

/-- A configuration event is measurable on any fixed subset of coordinate indices. -/
lemma measurableSet_subconfig {k : ℕ} (S : Finset (Fin k)) (f : α → β) (hf : Measurable f)
    (E : Multiset β → Prop) (hE : ∀ n, MeasurableSet {x : Fin n → β | E (config x)}) :
    MeasurableSet {x : Fin k → α | E (S.val.map (f ∘ x))} := by
  classical
  let l := S.val.toList
  let g : (Fin k → α) → Fin l.length → β := fun x j => f (x (l.get j))
  have hg : Measurable g := measurable_pi_iff.mpr fun j => hf.comp (measurable_pi_apply _)
  have he (x : Fin k → α) : config (g x) = S.val.map (f ∘ x) := by
    rw [config, Fin.univ_val_map]
    have hl : List.ofFn (g x) = l.map (f ∘ x) := by
      exact (List.map_ofFn (f := l.get) (g := f ∘ x)).symm.trans
        (congrArg (List.map (f ∘ x)) (List.ofFn_get l))
    rw [hl]
    simp only [← Multiset.map_coe, l, Multiset.coe_toList]
  have ht := (hE l.length).preimage hg
  simpa only [Set.preimage, mem_ofPred_eq, he] using ht

/-- **Tuple-event measurability survives measurable window restriction and marking.** -/
theorem measurableSet_window_event {k : ℕ} {B : Set α} (hB : MeasurableSet B)
    (f : α → β) (hf : Measurable f) (E : Multiset β → Prop)
    (hE : ∀ n, MeasurableSet {x : Fin n → β | E (config x)}) :
    MeasurableSet {x : Fin k → α | E ((inWindow B (config x)).map f)} := by
  classical
  let C : Finset (Fin k) → Set (Fin k → α) := fun S => {x | ∀ i, x i ∈ B ↔ i ∈ S}
  have hC (S : Finset (Fin k)) : MeasurableSet (C S) := by
    have hi (i : Fin k) : MeasurableSet {x : Fin k → α | x i ∈ B ↔ i ∈ S} := by
      by_cases h : i ∈ S
      · simpa only [h, iff_true, Set.preimage] using hB.preimage (measurable_pi_apply i)
      · simpa only [h, iff_false, Set.preimage, compl_ofPred] using
          (hB.preimage (measurable_pi_apply i)).compl
    convert MeasurableSet.iInter hi using 1
    ext x; simp [C]
  have hfilter (x : Fin k → α) : (inWindow B (config x)).map f =
      (Finset.univ.filter (fun i : Fin k => x i ∈ B)).val.map (f ∘ x) := by
    simp only [inWindow, config, Multiset.filter_map, Multiset.map_map, Finset.filter_val]
    rfl
  have hindices (S : Finset (Fin k)) {x : Fin k → α} (hx : x ∈ C S) :
      Finset.univ.filter (fun i : Fin k => x i ∈ B) = S := by
    ext i; simpa only [Finset.mem_filter, Finset.mem_univ, true_and] using hx i
  have he : {x : Fin k → α | E ((inWindow B (config x)).map f)} =
      ⋃ S : Finset (Fin k), C S ∩ {x | E (S.val.map (f ∘ x))} := by
    ext x
    simp only [mem_ofPred_eq, mem_iUnion, mem_inter_iff]
    constructor
    · intro hx
      refine ⟨Finset.univ.filter (fun i : Fin k => x i ∈ B), ?_, ?_⟩
      · intro i; simp
      · rwa [hfilter] at hx
    · rintro ⟨S, hx, hE⟩
      rwa [hfilter, hindices S hx]
  rw [he]
  exact MeasurableSet.iUnion fun S => (hC S).inter (measurableSet_subconfig S f hf E hE)

end PoissonPP
