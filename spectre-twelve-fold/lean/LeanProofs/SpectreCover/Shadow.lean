import Mathlib

/-!
# Shadows of oriented segments (MO 516016)

The analytic core of the 12-fold Spectre cover. For an oriented segment `P → Q` and a point `z`
whose `x`-coordinate lies strictly between those of `P` and `Q`, the *shadow* of the segment at `z`
is `-1` if the segment runs left to right above `z`, `+1` if it runs right to left above `z`,
and `0` otherwise. Reversing a segment negates its shadow, exactly (`shadow_swap`).

`tri_shadow`: for a counterclockwise triangle `ABC` and a point `z` on a column through no
vertex, off the three edges, the indicator of the closed triangle at `z` is the sum of the
shadows of its three edges. This is the indicator form of the trapezoid (shoelace) formula,
and it is what lets edge cancellation control a sum of indicators.
-/

namespace SpectreCover

/-- Twice the signed area of the triangle `p q r`. -/
def orient (p q r : ℝ × ℝ) : ℝ := (q.1 - p.1) * (r.2 - p.2) - (q.2 - p.2) * (r.1 - p.1)

/-- The closed triangle with vertices `A B C`, counterclockwise when `0 < orient A B C`. -/
def closedTri (A B C : ℝ × ℝ) : Set (ℝ × ℝ) :=
  {z | 0 ≤ orient A B z ∧ 0 ≤ orient B C z ∧ 0 ≤ orient C A z}

/-- The shadow of the oriented segment `P → Q` at `z`. -/
noncomputable def shadow (P Q z : ℝ × ℝ) : ℤ := by
  classical
  exact if P.1 < z.1 ∧ z.1 < Q.1 ∧ orient P Q z < 0 then -1
    else if Q.1 < z.1 ∧ z.1 < P.1 ∧ 0 < orient P Q z then 1 else 0

theorem orient_swap (p q r : ℝ × ℝ) : orient q p r = -orient p q r := by
  unfold orient; ring

theorem orient_cycle (p q r : ℝ × ℝ) : orient q r p = orient p q r := by
  unfold orient; ring

theorem shadow_swap (P Q z : ℝ × ℝ) : shadow Q P z = -shadow P Q z := by
  unfold shadow
  rw [orient_swap]
  by_cases hA : P.1 < z.1 ∧ z.1 < Q.1
  · have hB : ¬ Q.1 < z.1 := fun h => by linarith [hA.2]
    by_cases ho : orient P Q z < 0
    · have : 0 < -orient P Q z := by linarith
      simp [hA, hB, ho, this]
    · have : ¬ 0 < -orient P Q z := by linarith
      simp [hA, hB, ho, this]
  · by_cases hB : Q.1 < z.1 ∧ z.1 < P.1
    · have hA' : ¬ P.1 < z.1 := fun h => by linarith [hB.2]
      by_cases ho : 0 < orient P Q z
      · have : -orient P Q z < 0 := by linarith
        simp [hB, hA', ho, this]
      · have : ¬ -orient P Q z < 0 := by linarith
        simp [hB, hA', ho, this]
    · rw [ite_eq_right_of_eq_false _ _ (eq_false (fun h => hB ⟨h.1, h.2.1⟩)),
        ite_eq_right_of_eq_false _ _ (eq_false (fun h => hA ⟨h.1, h.2.1⟩)),
        ite_eq_right_of_eq_false _ _ (eq_false (fun h => hA ⟨h.1, h.2.1⟩)),
        ite_eq_right_of_eq_false _ _ (eq_false (fun h => hB ⟨h.1, h.2.1⟩))]
      simp

/-- Barycentric identity: `orient A B C • z = Σ (sub-orientation) • vertex`, first coordinate. -/
theorem bary_fst (A B C z : ℝ × ℝ) :
    orient A B C * z.1 = orient B C z * A.1 + orient C A z * B.1 + orient A B z * C.1 := by
  unfold orient; ring

theorem bary_snd (A B C z : ℝ × ℝ) :
    orient A B C * z.2 = orient B C z * A.2 + orient C A z * B.2 + orient A B z * C.2 := by
  unfold orient; ring

theorem bary_sum (A B C z : ℝ × ℝ) :
    orient A B z + orient B C z + orient C A z = orient A B C := by
  unfold orient; ring

/-- A point on the line `PQ` strictly inside its `x`-range lies on the segment. -/
theorem mem_segment_of_orient_zero {P Q z : ℝ × ℝ} (h0 : orient P Q z = 0)
    (hx : (P.1 < z.1 ∧ z.1 < Q.1) ∨ (Q.1 < z.1 ∧ z.1 < P.1)) : z ∈ segment ℝ P Q := by
  have hne : Q.1 - P.1 ≠ 0 := by rcases hx with h | h <;> intro h' <;> linarith [h.1, h.2]
  set t := (z.1 - P.1) / (Q.1 - P.1) with ht
  have ht0 : 0 ≤ t := by
    rcases hx with h | h
    · exact div_nonneg (by linarith [h.1]) (by linarith [h.2])
    · exact div_nonneg_of_nonpos (by linarith [h.2]) (by linarith [h.1])
  have ht1 : t ≤ 1 := by
    rcases hx with h | h
    · rw [div_le_one (by linarith [h.1, h.2])]; linarith [h.2]
    · rw [div_le_one_of_neg (by linarith [h.1, h.2])]; linarith [h.1]
  refine ⟨1 - t, t, by linarith, ht0, by ring, ?_⟩
  have hx1 : t * (Q.1 - P.1) = z.1 - P.1 := by rw [ht]; field_simp
  have hy1 : t * (Q.2 - P.2) = z.2 - P.2 := by
    unfold orient at h0
    have : (Q.1 - P.1) * (t * (Q.2 - P.2)) = (Q.1 - P.1) * (z.2 - P.2) := by
      linear_combination (Q.2 - P.2) * hx1 - h0
    exact mul_left_cancel₀ hne this
  ext
  · simp only [Prod.fst_add, Prod.smul_fst, smul_eq_mul]; linear_combination hx1
  · simp only [Prod.snd_add, Prod.smul_snd, smul_eq_mul]; linear_combination hy1

theorem shadow_eq_zero {P Q z : ℝ × ℝ}
    (h : ¬ ((P.1 < z.1 ∧ z.1 < Q.1) ∨ (Q.1 < z.1 ∧ z.1 < P.1))) : shadow P Q z = 0 := by
  unfold shadow
  rw [ite_eq_right_of_eq_false _ _ (eq_false (fun h' => h (Or.inl ⟨h'.1, h'.2.1⟩))),
    ite_eq_right_of_eq_false _ _ (eq_false (fun h' => h (Or.inr ⟨h'.1, h'.2.1⟩)))]

theorem mem_closedTri_cycle {A B C z : ℝ × ℝ} : z ∈ closedTri B C A ↔ z ∈ closedTri A B C := by
  simp only [closedTri, Set.mem_setOf_eq]; tauto

theorem bary_shift (A B C z : ℝ × ℝ) :
    orient A B C * (z.1 - A.1) = orient C A z * (B.1 - A.1) + orient A B z * (C.1 - A.1) := by
  unfold orient; ring

theorem bary_rest (A B C z : ℝ × ℝ) :
    orient B C z * (z.1 - A.1) = orient C A z * (B.1 - z.1) + orient A B z * (C.1 - z.1) := by
  unfold orient; ring

open Classical in
/-- The triangle identity when the column through `z` crosses the two edges at `A`. -/
theorem tri_key {A B C z : ℝ × ℝ} (hD : 0 < orient A B C)
    (hside : (A.1 < z.1 ∧ z.1 < B.1 ∧ z.1 < C.1) ∨ (B.1 < z.1 ∧ C.1 < z.1 ∧ z.1 < A.1))
    (sAB : z ∉ segment ℝ A B) (sCA : z ∉ segment ℝ C A) :
    (if z ∈ closedTri A B C then 1 else 0 : ℤ) = shadow A B z + shadow B C z + shadow C A z := by
  have key := bary_shift A B C z
  have rest := bary_rest A B C z
  have hBC : shadow B C z = 0 := shadow_eq_zero (by
    rcases hside with h | h <;> rintro (h' | h') <;> linarith [h.1, h.2.1, h.2.2, h'.1, h'.2])
  rw [hBC]
  simp only [closedTri, Set.mem_setOf_eq]
  rcases hside with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩
  · have eAB : shadow A B z = if orient A B z < 0 then -1 else 0 := by
      simp [shadow, h1, h2, not_lt.mpr h2.le]
    have eCA : shadow C A z = if 0 < orient C A z then 1 else 0 := by
      simp [shadow, h1, h3, not_lt.mpr h3.le]
    have nAB : orient A B z ≠ 0 := fun h0 => sAB (mem_segment_of_orient_zero h0 (Or.inl ⟨h1, h2⟩))
    have nCA : orient C A z ≠ 0 := fun h0 => sCA (mem_segment_of_orient_zero h0 (Or.inr ⟨h1, h3⟩))
    rw [eAB, eCA]
    set oAB := orient A B z
    set oBC := orient B C z
    set oCA := orient C A z
    rcases nAB.lt_or_gt with hab | hab <;> rcases nCA.lt_or_gt with hca | hca
    · exfalso
      nlinarith [mul_neg_of_neg_of_pos hca (by linarith : 0 < B.1 - A.1),
        mul_neg_of_neg_of_pos hab (by linarith : 0 < C.1 - A.1),
        mul_pos hD (by linarith : 0 < z.1 - A.1)]
    · simp [hab, hca, not_le.mpr hab]
    · simp [hca.le, not_le.mpr hca, not_lt.mpr hab.le]
    · have hbc : 0 < oBC := by
        have k1 := mul_pos hca (by linarith : 0 < B.1 - z.1)
        have k2 := mul_pos hab (by linarith : 0 < C.1 - z.1)
        have k3 : 0 < oBC * (z.1 - A.1) := by linarith
        exact pos_of_mul_pos_left k3 (by linarith)
      simp [hab.le, hca.le, hbc.le, hca, not_lt.mpr hab.le]
  · have eAB : shadow A B z = if 0 < orient A B z then 1 else 0 := by
      simp [shadow, h1, h3, not_lt.mpr h3.le]
    have eCA : shadow C A z = if orient C A z < 0 then -1 else 0 := by
      simp [shadow, h2, h3, not_lt.mpr h3.le]
    have nAB : orient A B z ≠ 0 := fun h0 => sAB (mem_segment_of_orient_zero h0 (Or.inr ⟨h1, h3⟩))
    have nCA : orient C A z ≠ 0 := fun h0 => sCA (mem_segment_of_orient_zero h0 (Or.inl ⟨h2, h3⟩))
    rw [eAB, eCA]
    set oAB := orient A B z
    set oBC := orient B C z
    set oCA := orient C A z
    rcases nAB.lt_or_gt with hab | hab <;> rcases nCA.lt_or_gt with hca | hca
    · exfalso
      nlinarith [mul_pos_of_neg_of_neg hca (by linarith : B.1 - A.1 < 0),
        mul_pos_of_neg_of_neg hab (by linarith : C.1 - A.1 < 0),
        mul_pos hD (by linarith : 0 < A.1 - z.1)]
    · simp [hab.le, not_le.mpr hab, not_lt.mpr hca.le]
    · simp [hab, hca, not_le.mpr hca]
    · have hbc : 0 < oBC := by
        have k1 := mul_pos hca (by linarith : 0 < z.1 - B.1)
        have k2 := mul_pos hab (by linarith : 0 < z.1 - C.1)
        have k3 : 0 < oBC * (A.1 - z.1) := by linarith
        exact pos_of_mul_pos_left k3 (by linarith)
      simp [hab.le, hca.le, hbc.le, hab, not_lt.mpr hca.le]

/-- A closed triangle lies in the vertical strip spanned by its vertices. -/
theorem not_mem_closedTri_of_left {A B C z : ℝ × ℝ} (hD : 0 < orient A B C)
    (ha : A.1 < z.1) (hb : B.1 < z.1) (hc : C.1 < z.1) : z ∉ closedTri A B C := by
  rintro ⟨h1, h2, h3⟩
  have hx := bary_fst A B C z
  have hs := bary_sum A B C z
  set δ := min (min (z.1 - A.1) (z.1 - B.1)) (z.1 - C.1)
  have hδ : 0 < δ := lt_min (lt_min (by linarith) (by linarith)) (by linarith)
  have dA : δ ≤ z.1 - A.1 := (min_le_left _ _).trans (min_le_left _ _)
  have dB : δ ≤ z.1 - B.1 := (min_le_left _ _).trans (min_le_right _ _)
  have dC : δ ≤ z.1 - C.1 := min_le_right _ _
  have e1 := congrArg (· * z.1) hs
  have e2 := congrArg (· * δ) hs
  nlinarith [mul_le_mul_of_nonneg_left dA h2, mul_le_mul_of_nonneg_left dB h3,
    mul_le_mul_of_nonneg_left dC h1, mul_pos hD hδ]

theorem not_mem_closedTri_of_right {A B C z : ℝ × ℝ} (hD : 0 < orient A B C)
    (ha : z.1 < A.1) (hb : z.1 < B.1) (hc : z.1 < C.1) : z ∉ closedTri A B C := by
  rintro ⟨h1, h2, h3⟩
  have hx := bary_fst A B C z
  have hs := bary_sum A B C z
  set δ := min (min (A.1 - z.1) (B.1 - z.1)) (C.1 - z.1)
  have hδ : 0 < δ := lt_min (lt_min (by linarith) (by linarith)) (by linarith)
  have dA : δ ≤ A.1 - z.1 := (min_le_left _ _).trans (min_le_left _ _)
  have dB : δ ≤ B.1 - z.1 := (min_le_left _ _).trans (min_le_right _ _)
  have dC : δ ≤ C.1 - z.1 := min_le_right _ _
  have e1 := congrArg (· * z.1) hs
  have e2 := congrArg (· * δ) hs
  nlinarith [mul_le_mul_of_nonneg_left dA h2, mul_le_mul_of_nonneg_left dB h3,
    mul_le_mul_of_nonneg_left dC h1, mul_pos hD hδ]

open Classical in
/-- **Triangle identity.** On a column through no vertex, off the edges, the indicator of a
counterclockwise closed triangle is the sum of the shadows of its edges. -/
theorem tri_shadow {A B C z : ℝ × ℝ} (hD : 0 < orient A B C)
    (hA : A.1 ≠ z.1) (hB : B.1 ≠ z.1) (hC : C.1 ≠ z.1)
    (sAB : z ∉ segment ℝ A B) (sBC : z ∉ segment ℝ B C) (sCA : z ∉ segment ℝ C A) :
    (if z ∈ closedTri A B C then 1 else 0 : ℤ) = shadow A B z + shadow B C z + shadow C A z := by
  have hD2 : 0 < orient B C A := by rw [orient_cycle]; exact hD
  have hD3 : 0 < orient C A B := by rw [orient_cycle, orient_cycle]; exact hD
  have m2 : z ∈ closedTri B C A ↔ z ∈ closedTri A B C := mem_closedTri_cycle
  have m3 : z ∈ closedTri C A B ↔ z ∈ closedTri A B C :=
    mem_closedTri_cycle.trans mem_closedTri_cycle
  have z0 : ∀ {P Q : ℝ × ℝ}, (P.1 < z.1 ∧ Q.1 < z.1) ∨ (z.1 < P.1 ∧ z.1 < Q.1) →
      shadow P Q z = 0 := fun h => shadow_eq_zero (by
    rcases h with h | h <;> rintro (h' | h') <;> linarith [h.1, h.2, h'.1, h'.2])
  rcases hA.lt_or_gt with a | a <;> rcases hB.lt_or_gt with b | b <;> rcases hC.lt_or_gt with c | c
  · rw [ite_eq_right_of_eq_false _ _ (eq_false (not_mem_closedTri_of_left hD a b c)),
      z0 (Or.inl ⟨a, b⟩), z0 (Or.inl ⟨b, c⟩),
      z0 (Or.inl ⟨c, a⟩)]; rfl
  · have := tri_key hD3 (Or.inr ⟨a, b, c⟩) sCA sBC
    rw [m3] at this; rw [this]; ring
  · have := tri_key hD2 (Or.inr ⟨c, a, b⟩) sBC sAB
    rw [m2] at this; rw [this]; ring
  · exact tri_key hD (Or.inl ⟨a, b, c⟩) sAB sCA
  · exact tri_key hD (Or.inr ⟨b, c, a⟩) sAB sCA
  · have := tri_key hD2 (Or.inl ⟨b, c, a⟩) sBC sAB
    rw [m2] at this; rw [this]; ring
  · have := tri_key hD3 (Or.inl ⟨c, a, b⟩) sCA sBC
    rw [m3] at this; rw [this]; ring
  · rw [ite_eq_right_of_eq_false _ _ (eq_false (not_mem_closedTri_of_right hD a b c)),
      z0 (Or.inr ⟨a, b⟩), z0 (Or.inr ⟨b, c⟩),
      z0 (Or.inr ⟨c, a⟩)]; rfl

end SpectreCover
