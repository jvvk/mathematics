import LeanProofs.TwoTri.Basic

/-!
# Crossing segments meet, and meeting segments cross
-/

set_option linter.unusedSectionVars false

namespace TwoTri

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-- Crossing segments have a common point, interior to both. -/
lemma SCross.meet {a b c d : K × K} (h : SCross a b c d) :
    ∃ t s : K, 0 < t ∧ t < 1 ∧ 0 < s ∧ s < 1 ∧ lerp a b t = lerp c d s := by
  obtain ⟨h1, h2⟩ := h
  set U := orient a b c
  set V := orient a b d
  set X := orient c d a
  set Y := orient c d b
  have hXY : X - Y ≠ 0 := by intro h0; have : X = Y := by linarith
                             rw [this] at h2; nlinarith [mul_self_nonneg Y]
  have hUV : U - V ≠ 0 := by intro h0; have : U = V := by linarith
                             rw [this] at h1; nlinarith [mul_self_nonneg V]
  refine ⟨X / (X - Y), U / (U - V), ?_, ?_, ?_, ?_, ?_⟩
  · rcases lt_or_gt_of_ne hXY with h | h
    · exact div_pos_of_neg_of_neg (by nlinarith) h
    · exact div_pos (by nlinarith) h
  · rcases lt_or_gt_of_ne hXY with h | h
    · rw [div_lt_one_of_neg h]; nlinarith
    · rw [div_lt_one h]; nlinarith
  · rcases lt_or_gt_of_ne hUV with h | h
    · exact div_pos_of_neg_of_neg (by nlinarith) h
    · exact div_pos (by nlinarith) h
  · rcases lt_or_gt_of_ne hUV with h | h
    · rw [div_lt_one_of_neg h]; nlinarith
    · rw [div_lt_one h]; nlinarith
  · simp only [U, V, X, Y] at hXY hUV ⊢
    unfold lerp
    ext
    · simp only; field_simp; unfold orient; ring
    · simp only; field_simp; unfold orient; ring

/-- Segments that meet, with endpoints in general position, cross. -/
lemma scross_of_meet {a b c d : K × K} (hc : orient a b c ≠ 0) (hd : orient a b d ≠ 0)
    (ha : orient c d a ≠ 0) (hb : orient c d b ≠ 0) {t s : K} (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (e : lerp a b t = lerp c d s) : SCross a b c d := by
  have E1 : (1 - s) * orient a b c + s * orient a b d = 0 := by
    rw [← orient_lerp, ← e, orient_lerp_self]
  have E2 : (1 - t) * orient c d a + t * orient c d b = 0 := by
    rw [← orient_lerp, e, orient_lerp_self]
  have hs : 0 < s := lt_of_le_of_ne hs0 (by rintro rfl; simp at E1; exact hc E1)
  have hs' : s < 1 := lt_of_le_of_ne hs1 (by rintro rfl; simp at E1; exact hd E1)
  have ht : 0 < t := lt_of_le_of_ne ht0 (by rintro rfl; simp at E2; exact ha E2)
  have ht' : t < 1 := lt_of_le_of_ne ht1 (by rintro rfl; simp at E2; exact hb E2)
  exact ⟨mul_neg_of_comb_zero hs hs' hd E1, mul_neg_of_comb_zero ht ht' hb E2⟩

/-- A point on the line `u v` with positive orientation against the other two sides of the
counterclockwise triangle `u v o` lies strictly between `u` and `v`. -/
lemma on_side {u v o m : K × K} (h0 : orient u v m = 0) (h1 : 0 < orient v o m)
    (h2 : 0 < orient o u m) : ∃ σ : K, 0 < σ ∧ σ < 1 ∧ m = lerp u v σ := by
  have hS := orient_sum u v o m
  have hD : 0 < orient u v o := by linarith
  set σ := orient o u m / orient u v o with hσdef
  have hσ : orient u v o * σ = orient o u m := mul_div_cancel₀ _ hD.ne'
  refine ⟨σ, div_pos h2 hD, (div_lt_one hD).mpr (by linarith), ?_⟩
  have e1 := bary_fst u v o m
  have e2 := bary_snd u v o m
  unfold lerp
  ext
  · apply mul_left_cancel₀ hD.ne'
    simp only
    linear_combination e1 + u.1 * hS - u.1 * h0 - (v.1 - u.1) * hσ + o.1 * h0
  · apply mul_left_cancel₀ hD.ne'
    simp only
    linear_combination e2 + u.2 * hS - u.2 * h0 - (v.2 - u.2) * hσ + o.2 * h0

/-- A point on two side lines of a nondegenerate triangle is their common vertex. -/
lemma eq_vertex {x y z m : K × K} (hD : orient x y z ≠ 0) (h1 : orient x y m = 0)
    (h2 : orient y z m = 0) : m = y := by
  have hS := orient_sum x y z m
  have e1 := bary_fst x y z m
  have e2 := bary_snd x y z m
  rw [h1, h2] at e1 e2
  have h3 : orient z x m = orient x y z := by linarith
  rw [h3] at e1 e2
  ext
  · exact mul_left_cancel₀ hD (by linarith)
  · exact mul_left_cancel₀ hD (by linarith)

end TwoTri
