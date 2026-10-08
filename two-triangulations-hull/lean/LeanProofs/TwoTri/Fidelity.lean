import LeanProofs.TwoTri.Main
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional

/-!
# The definitions mean what the paper says

* `orient a b c = 0` iff `a, b, c` are collinear (Mathlib's `Collinear`), so `GenPos` is "no three
  points on a line";
* for points in general position, `Cross` is "the closed segments, with four distinct endpoints,
  meet" (Mathlib's `segment`);
* hence `IsTri` is the paper's definition of a triangulation, a maximal set of pairwise
  non-crossing segments, and Theorem 1 holds verbatim with these geometric notions.
-/

set_option linter.unusedSectionVars false

namespace TwoTri

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

lemma orient_eq_zero_iff_collinear {a b c : K × K} (hab : a ≠ b) :
    orient a b c = 0 ↔ Collinear K ({a, b, c} : Set (K × K)) := by
  rw [collinear_iff_of_mem (p₀ := a) (by simp)]
  constructor
  · intro h
    set u := b - a
    have hu : u.1 * u.1 + u.2 * u.2 ≠ 0 := by
      intro h0
      apply hab
      have h1 : u.1 = 0 := by nlinarith [mul_self_nonneg u.1, mul_self_nonneg u.2]
      have h2 : u.2 = 0 := by nlinarith [mul_self_nonneg u.1, mul_self_nonneg u.2]
      ext
      · have : (b - a).1 = 0 := h1; simp at this; linarith
      · have : (b - a).2 = 0 := h2; simp at this; linarith
    refine ⟨u, ?_⟩
    intro p hp
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp
    rcases hp with rfl | rfl | rfl
    · exact ⟨0, by simp⟩
    · exact ⟨1, by simp [u]⟩
    · set D := u.1 * u.1 + u.2 * u.2
      set N := (p.1 - a.1) * u.1 + (p.2 - a.2) * u.2
      have hu1 : u.1 = b.1 - a.1 := rfl
      have hu2 : u.2 = b.2 - a.2 := rfl
      refine ⟨N / D, ?_⟩
      unfold orient at h
      rw [← hu1, ← hu2] at h
      ext
      · simp only [vadd_eq_add, Prod.fst_add, Prod.smul_fst, smul_eq_mul]
        rw [div_mul_eq_mul_div, div_add' _ _ _ hu, eq_div_iff hu]
        simp only [N, D]
        linear_combination (-u.2) * h
      · simp only [vadd_eq_add, Prod.snd_add, Prod.smul_snd, smul_eq_mul]
        rw [div_mul_eq_mul_div, div_add' _ _ _ hu, eq_div_iff hu]
        simp only [N, D]
        linear_combination u.1 * h
  · rintro ⟨v, hv⟩
    obtain ⟨r, hr⟩ := hv b (by simp)
    obtain ⟨s, hs⟩ := hv c (by simp)
    rw [vadd_eq_add] at hr hs
    have e1 := congrArg Prod.fst hr; have e2 := congrArg Prod.snd hr
    have e3 := congrArg Prod.fst hs; have e4 := congrArg Prod.snd hs
    simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul] at e1 e2 e3 e4
    unfold orient
    rw [e1, e2, e3, e4]; ring

/-- `GenPos` is exactly "no three distinct points of `P` are collinear". -/
theorem genPos_iff {P : Finset (K × K)} :
    GenPos P ↔ ∀ a ∈ P, ∀ b ∈ P, ∀ c ∈ P, a ≠ b → a ≠ c → b ≠ c →
      ¬ Collinear K ({a, b, c} : Set (K × K)) := by
  constructor
  · intro h a ha b hb c hc hab hac hbc hcol
    exact h a ha b hb c hc hab hac hbc ((orient_eq_zero_iff_collinear hab).mpr hcol)
  · intro h a ha b hb c hc hab hac hbc h0
    exact h a ha b hb c hc hab hac hbc ((orient_eq_zero_iff_collinear hab).mp h0)

lemma lerp_mem_segment {a b : K × K} {t : K} (h0 : 0 ≤ t) (h1 : t ≤ 1) :
    lerp a b t ∈ segment K a b := by
  rw [segment_eq_image, lerp_eq_smul]; exact ⟨t, ⟨h0, h1⟩, rfl⟩

lemma exists_lerp_of_mem_segment {a b z : K × K} (h : z ∈ segment K a b) :
    ∃ t, 0 ≤ t ∧ t ≤ 1 ∧ z = lerp a b t := by
  rw [segment_eq_image] at h
  obtain ⟨t, ⟨h0, h1⟩, rfl⟩ := h
  exact ⟨t, h0, h1, (lerp_eq_smul _ _ _).symm⟩

/-- For endpoints in general position, the sign test is "the closed segments meet". -/
theorem scross_iff_meet {a b c d : K × K} (h1 : orient a b c ≠ 0) (h2 : orient a b d ≠ 0)
    (h3 : orient c d a ≠ 0) (h4 : orient c d b ≠ 0) :
    SCross a b c d ↔ (segment K a b ∩ segment K c d).Nonempty := by
  constructor
  · intro h
    obtain ⟨t, s, ht0, ht1, hs0, hs1, e⟩ := h.meet
    exact ⟨lerp a b t, lerp_mem_segment ht0.le ht1.le, e ▸ lerp_mem_segment hs0.le hs1.le⟩
  · rintro ⟨z, hz1, hz2⟩
    obtain ⟨t, ht0, ht1, rfl⟩ := exists_lerp_of_mem_segment hz1
    obtain ⟨s, hs0, hs1, e⟩ := exists_lerp_of_mem_segment hz2
    exact scross_of_meet h1 h2 h3 h4 ht0 ht1 hs0 hs1 e

/-- The geometric notion: two segments with four distinct endpoints whose closed segments meet. -/
def CrossG (s t : Sym2 (K × K)) : Prop :=
  ∃ a b c d, s = s(a, b) ∧ t = s(c, d) ∧ a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d ∧
    (segment K a b ∩ segment K c d).Nonempty

/-- For segments of a general-position set, `Cross` is `CrossG`. -/
theorem cross_iff_crossG {P : Finset (K × K)} (hP : GenPos P) {s t : Sym2 (K × K)}
    (hs : s ∈ segs P) (ht : t ∈ segs P) : Cross s t ↔ CrossG s t := by
  constructor
  · intro h
    induction s using Sym2.ind with
    | _ a b =>
    induction t using Sym2.ind with
    | _ c d =>
      obtain ⟨ha, hb, hab⟩ := mk_mem_segs.mp hs
      obtain ⟨hc, hd, hcd⟩ := mk_mem_segs.mp ht
      have hx := cross_mk.mp h
      have o1 : orient a b c ≠ 0 := fun e => by have := hx.1; rw [e] at this; simp at this
      have o2 : orient a b d ≠ 0 := fun e => by have := hx.1; rw [e] at this; simp at this
      have o3 : orient c d a ≠ 0 := fun e => by have := hx.2; rw [e] at this; simp at this
      have o4 : orient c d b ≠ 0 := fun e => by have := hx.2; rw [e] at this; simp at this
      refine ⟨a, b, c, d, rfl, rfl, hab, ?_, ?_, ?_, ?_, hcd, (scross_iff_meet o1 o2 o3 o4).mp hx⟩
      · rintro rfl; simp at o3
      · rintro rfl; simp at o3
      · rintro rfl; simp at o4
      · rintro rfl; simp at o4
  · rintro ⟨a, b, c, d, rfl, rfl, hab, hac, had, hbc, hbd, hcd, hm⟩
    obtain ⟨ha, hb, -⟩ := mk_mem_segs.mp hs
    obtain ⟨hc, hd, -⟩ := mk_mem_segs.mp ht
    rw [cross_mk]
    exact (scross_iff_meet (hP a ha b hb c hc hab hac hbc) (hP a ha b hb d hd hab had hbd)
      (hP c hc d hd a ha hcd (Ne.symm hac) (Ne.symm had))
      (hP c hc d hd b hb hcd (Ne.symm hbc) (Ne.symm hbd))).mpr hm

/-- The paper's definition of a triangulation, with the geometric crossing relation. -/
def IsTriG (P : Finset (K × K)) (T : Finset (Sym2 (K × K))) : Prop :=
  T ⊆ segs P ∧ (∀ s ∈ T, ∀ t ∈ T, ¬ CrossG s t) ∧ ∀ s ∈ segs P, s ∉ T → ∃ t ∈ T, CrossG s t

theorem isTriG_iff {P : Finset (K × K)} (hP : GenPos P) {T : Finset (Sym2 (K × K))} :
    IsTriG P T ↔ IsTri P T := by
  constructor
  · rintro ⟨h1, h2, h3⟩
    refine ⟨h1, fun s hs t ht hc => h2 s hs t ht ((cross_iff_crossG hP (h1 hs) (h1 ht)).mp hc),
      fun s hs hn => ?_⟩
    obtain ⟨t, ht, hc⟩ := h3 s hs hn
    exact ⟨t, ht, (cross_iff_crossG hP hs (h1 ht)).mpr hc⟩
  · rintro ⟨h1, h2, h3⟩
    refine ⟨h1, fun s hs t ht hc => h2 s hs t ht ((cross_iff_crossG hP (h1 hs) (h1 ht)).mpr hc),
      fun s hs hn => ?_⟩
    obtain ⟨t, ht, hc⟩ := h3 s hs hn
    exact ⟨t, ht, (cross_iff_crossG hP hs (h1 ht)).mp hc⟩

/-- **Theorem 1, geometric statement.** For every `n ≥ 9` there are `n` points in `ℝ²`, no three
collinear, with five hull edges, carrying two maximal sets of pairwise non-crossing segments
whose only common segments are the hull edges; and any two such maximal sets on any `n ≥ 5`
points with no three collinear share at least five segments. -/
theorem theorem1_geometric (n : ℕ) (hn : 9 ≤ n) :
    (∃ P : Finset (ℝ × ℝ), P.card = n ∧
      (∀ a ∈ P, ∀ b ∈ P, ∀ c ∈ P, a ≠ b → a ≠ c → b ≠ c → ¬ Collinear ℝ ({a, b, c} : Set _)) ∧
      (hullEdges P).card = 5 ∧
      ∃ A B, IsTriG P A ∧ IsTriG P B ∧ A ∩ B = hullEdges P) ∧
    ∀ P : Finset (ℝ × ℝ), P.card = n →
      (∀ a ∈ P, ∀ b ∈ P, ∀ c ∈ P, a ≠ b → a ≠ c → b ≠ c → ¬ Collinear ℝ ({a, b, c} : Set _)) →
      ∀ A B, IsTriG P A → IsTriG P B → 5 ≤ (A ∩ B).card := by
  refine ⟨?_, fun P hc hg A B hA hB => ?_⟩
  · obtain ⟨⟨P, hc, hP, hh, A, B, hA, hB, hAB⟩, -⟩ := theorem1 n hn
    exact ⟨P, hc, genPos_iff.mp hP, hh, A, B, (isTriG_iff hP).mpr hA, (isTriG_iff hP).mpr hB, hAB⟩
  · have hP := genPos_iff.mpr hg
    exact (lower hP (by omega) ((isTriG_iff hP).mp hA) ((isTriG_iff hP).mp hB)).1

end TwoTri
