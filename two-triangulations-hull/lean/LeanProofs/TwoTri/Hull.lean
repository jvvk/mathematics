import LeanProofs.TwoTri.Preserve

/-!
# Hull vertices and their hull neighbours

A point `u` is *exposed* if some linear functional is strictly larger at every other point.
An exposed point has a hull edge on each side: a neighbour `v` with every other point strictly
left of `u → v`, and a neighbour `w` with every other point strictly left of `w → u`. Endpoints
of hull edges are exposed, and some point is exposed.
-/

set_option linter.unusedSectionVars false

namespace TwoTri

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-- `d · (r - u)`. -/
def dotd (d u r : K × K) : K := d.1 * (r.1 - u.1) + d.2 * (r.2 - u.2)

/-- Every other point of `P` is strictly on the positive side of a line through `u`. -/
def Exposed (P : Finset (K × K)) (u : K × K) : Prop :=
  ∃ d : K × K, ∀ r ∈ P, r ≠ u → 0 < dotd d u r

lemma hullPos_not_both {P : Finset (K × K)} {a b c : K × K} (hc : c ∈ P) (hca : c ≠ a)
    (hcb : c ≠ b) (h1 : HullPos P a b) (h2 : HullPos P b a) : False := by
  have e1 := h1 c hc hca hcb
  have e2 := h2 c hc hcb hca
  rw [orient_swap12] at e2; linarith

/-- An exposed point of a set with at least three points has a left and a right hull
neighbour. -/
lemma Exposed.neighbours {P : Finset (K × K)} (hP : GenPos P) {u : K × K} (hu : u ∈ P)
    (he : Exposed P u) (h2 : 2 ≤ (P.erase u).card) :
    ∃ v w, v ∈ P ∧ w ∈ P ∧ v ≠ u ∧ w ≠ u ∧ HullPos P u v ∧ HullPos P w u := by
  obtain ⟨d, hd⟩ := he
  set S := P.erase u
  have hS : S.Nonempty := Finset.card_pos.mp (by omega)
  set s : K × K → K := fun r => dotd d u r
  set t : K × K → K := fun r => -d.2 * (r.1 - u.1) + d.1 * (r.2 - u.2)
  have spos : ∀ r ∈ S, 0 < s r := fun r hr =>
    hd r (Finset.mem_of_mem_erase hr) (Finset.ne_of_mem_erase hr)
  have hd2 : 0 < d.1 * d.1 + d.2 * d.2 := by
    obtain ⟨r, hr⟩ := hS
    have := spos r hr
    by_contra hc; push Not at hc
    have h1 : d.1 = 0 := by nlinarith [mul_self_nonneg d.1, mul_self_nonneg d.2]
    have h2' : d.2 = 0 := by nlinarith [mul_self_nonneg d.1, mul_self_nonneg d.2]
    simp only [s, dotd, h1, h2', zero_mul, add_zero] at this; exact lt_irrefl _ this
  have key : ∀ a b, orient u a b * (d.1 * d.1 + d.2 * d.2) = s a * t b - t a * s b := by
    intro a b; simp only [s, t, dotd, orient]; ring
  set g : K × K → K := fun r => t r / s r
  have lt_iff : ∀ a ∈ S, ∀ b ∈ S, (0 < orient u a b ↔ g a < g b) := by
    intro a ha b hb
    have sa := spos a ha; have sb := spos b hb
    simp only [g]
    rw [div_lt_div_iff₀ sa sb]
    constructor
    · intro h; have := mul_pos h hd2; rw [key] at this; linarith
    · intro h
      have : 0 < orient u a b * (d.1 * d.1 + d.2 * d.2) := by rw [key]; linarith
      exact pos_of_mul_pos_left this hd2.le
  obtain ⟨v, hv, hvmin⟩ := S.exists_min_image g hS
  obtain ⟨w, hw, hwmax⟩ := S.exists_max_image g hS
  have hvP := Finset.mem_of_mem_erase hv
  have hwP := Finset.mem_of_mem_erase hw
  have hvu := Finset.ne_of_mem_erase hv
  have hwu := Finset.ne_of_mem_erase hw
  refine ⟨v, w, hvP, hwP, hvu, hwu, ?_, ?_⟩
  · intro b hb hbu hbv
    have hbS : b ∈ S := Finset.mem_erase.mpr ⟨hbu, hb⟩
    have hne : orient u v b ≠ 0 := hP u hu v hvP b hb (Ne.symm hvu) (Ne.symm hbu) (Ne.symm hbv)
    rcases lt_or_gt_of_ne hne with h | h
    · exfalso
      have : 0 < orient u b v := by rw [orient_swap23]; linarith
      have := (lt_iff b hbS v hv).mp this
      linarith [hvmin b hbS]
    · exact h
  · intro b hb hbw hbu
    have hbS : b ∈ S := Finset.mem_erase.mpr ⟨hbu, hb⟩
    rw [orient_cyc]
    have hne : orient u b w ≠ 0 := hP u hu b hb w hwP (Ne.symm hbu) (Ne.symm hwu) hbw
    rcases lt_or_gt_of_ne hne with h | h
    · exfalso
      have : 0 < orient u w b := by rw [orient_swap23]; linarith
      have := (lt_iff w hw b hbS).mp this
      linarith [hwmax b hbS]
    · exact h

/-- Both endpoints of a hull edge are exposed. -/
lemma HullPos.exposed {P : Finset (K × K)} {a b : K × K} (hab : a ≠ b) (h : HullPos P a b) :
    Exposed P a ∧ Exposed P b := by
  classical
  have hn : 0 < (b.1 - a.1) * (b.1 - a.1) + (b.2 - a.2) * (b.2 - a.2) := by
    by_contra hc; push Not at hc
    apply hab; ext <;> nlinarith [mul_self_nonneg (b.1 - a.1), mul_self_nonneg (b.2 - a.2)]
  set F := (P.erase a).erase b
  have hF : ∀ r ∈ F, 0 < orient a b r := by
    intro r hr
    exact h r (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hr))
      (Finset.ne_of_mem_erase (Finset.mem_of_mem_erase hr)) (Finset.ne_of_mem_erase hr)
  constructor
  · obtain ⟨ε, hε, hεF, -⟩ := exists_small F (∅ : Finset Unit) (fun r => orient a b r)
      (fun r => (b.1 - a.1) * (r.1 - a.1) + (b.2 - a.2) * (r.2 - a.2)) (fun _ => 1)
      (fun _ => 0) hF (by simp)
    refine ⟨(-(b.2 - a.2) + ε * (b.1 - a.1), (b.1 - a.1) + ε * (b.2 - a.2)), ?_⟩
    intro r hr hra
    by_cases hrb : r = b
    · subst hrb; simp only [dotd]; nlinarith
    · have := hεF r (Finset.mem_erase.mpr ⟨hrb, Finset.mem_erase.mpr ⟨hra, hr⟩⟩)
      simp only [dotd]; unfold orient at this; linarith
  · obtain ⟨ε, hε, hεF, -⟩ := exists_small F (∅ : Finset Unit) (fun r => orient a b r)
      (fun r => (a.1 - b.1) * (r.1 - b.1) + (a.2 - b.2) * (r.2 - b.2)) (fun _ => 1)
      (fun _ => 0) hF (by simp)
    refine ⟨(-(b.2 - a.2) + ε * (a.1 - b.1), (b.1 - a.1) + ε * (a.2 - b.2)), ?_⟩
    intro r hr hrb
    by_cases hra : r = a
    · subst hra; simp only [dotd]; nlinarith
    · have := hεF r (Finset.mem_erase.mpr ⟨hrb, Finset.mem_erase.mpr ⟨hra, hr⟩⟩)
      simp only [dotd]; unfold orient at this; linarith

/-- Some point of a nonempty set is exposed. -/
lemma exists_exposed {P : Finset (K × K)} (hne : P.Nonempty) : ∃ u ∈ P, Exposed P u := by
  classical
  obtain ⟨u0, hu0, hmin1⟩ := P.exists_min_image (fun r => r.1) hne
  set S := P.filter (fun r => r.1 = u0.1)
  have hS : S.Nonempty := ⟨u0, Finset.mem_filter.mpr ⟨hu0, rfl⟩⟩
  obtain ⟨u, hu, hmin2⟩ := S.exists_min_image (fun r => r.2) hS
  obtain ⟨huP, hu1⟩ := Finset.mem_filter.mp hu
  set F := P.filter (fun r => u.1 < r.1)
  obtain ⟨ε, hε, hεF, -⟩ := exists_small F (∅ : Finset Unit) (fun r => r.1 - u.1)
    (fun r => r.2 - u.2) (fun _ => 1) (fun _ => 0)
    (fun r hr => sub_pos.mpr (Finset.mem_filter.mp hr).2) (by simp)
  refine ⟨u, huP, (1, ε), fun r hr hru => ?_⟩
  simp only [dotd, one_mul]
  have h1 : u.1 ≤ r.1 := by rw [hu1]; exact hmin1 r hr
  rcases h1.lt_or_eq with h1 | h1
  · have := hεF r (Finset.mem_filter.mpr ⟨hr, h1⟩); linarith
  · have hrS : r ∈ S := Finset.mem_filter.mpr ⟨hr, by rw [← h1, hu1]⟩
    have h2 : u.2 ≤ r.2 := hmin2 r hrS
    have h2' : u.2 < r.2 := lt_of_le_of_ne h2 (fun e => hru (Prod.ext h1.symm e.symm))
    rw [h1, sub_self]; nlinarith

end TwoTri
