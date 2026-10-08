import RandomChords.Centres

/-!
# Lemma 2 in terms of the offsets, and the direction of `AB`

`lemma2_offsets`: the offsets `x_A = cos θ_A`, `x_B = cos θ_B` are independent, each with the arcsine
law (the law of `cos U`, `U` uniform). `direction_law`: the cosine of the normal's angle with the line
of centres has the law of `(a cos U - b cos V) / D` (the remark after Lemma 2).
-/

open Real MeasureTheory Set
open scoped ENNReal

noncomputable section

namespace Chords

variable {a b D : ℝ}

/-- The offsets `(x_A, x_B)` of the line `AB` from the two centres. -/
def offsets2 (a b D : ℝ) (ω : Ang × Ang) : ℝ × ℝ :=
  (off (nrm (pt (-D) a ω.1) (pt 0 b ω.2)) (pt (-D) a ω.1) (-D, 0) a,
   off (nrm (pt (-D) a ω.1) (pt 0 b ω.2)) (pt 0 b ω.2) (0, 0) b)

/-- The arcsine law: `cos U` for `U` uniform on `(0, π)` (unnormalised, mass `π`). -/
def arcsine : Measure ℝ := (volume.restrict (Ioo 0 π)).map cos

lemma offsets2_eq (ha : 0 < a) (hb : 0 < b) (ω : Ang × Ang) (hω : pt (-D) a ω.1 ≠ pt 0 b ω.2) :
    offsets2 a b D ω = (fun x : ℝ × ℝ => (cos x.1, cos x.2)) (angles2 a b D ω) := by
  have hm := nrmD_unit (sub_ne_zero.2 (Ne.symm hω))
  obtain ⟨hA1, hA2⟩ := abs_off_le' hm (-D) a ha ω.1
  obtain ⟨hB1, hB2⟩ := abs_off_le' hm 0 b hb ω.2
  simp only [offsets2, angles2, nrm] at *
  rw [cos_arccos hA1 hA2, cos_arccos hB1 hB2]

/-- **Lemma 2, offsets form.** `x_A` and `x_B` are independent, each with the arcsine law. -/
theorem lemma2_offsets (ha : 0 < a) (hb : 0 < b) (hD : a + b ≤ D) :
    Measure.map (offsets2 a b D) volume = (4 : ℝ≥0∞) • arcsine.prod arcsine := by
  obtain ⟨hmap, hae⟩ := lemma2 ha hb hD
  have hc : Measurable (fun x : ℝ × ℝ => (cos x.1, cos x.2)) := by fun_prop
  rw [Measure.map_congr (g := (fun x : ℝ × ℝ => (cos x.1, cos x.2)) ∘ angles2 a b D)
      (by filter_upwards [hae] with ω hω using offsets2_eq ha hb ω hω),
    ← Measure.map_map hc (measurable_angles2 a b D), hmap, Measure.map_smul, restrict_sq,
    arcsine, Measure.map_prod_map _ _ continuous_cos.measurable continuous_cos.measurable]
  · rfl
  · exact hc.aemeasurable

/-- **The direction of `AB`.** The cosine of the normal's angle with the line of centres has the law
of `(a cos U - b cos V) / D`. -/
theorem direction_law (ha : 0 < a) (hb : 0 < b) (hD : a + b ≤ D) :
    Measure.map (fun ω : Ang × Ang => (nrm (pt (-D) a ω.1) (pt 0 b ω.2)).1) volume =
      (4 : ℝ≥0∞) • (volume.restrict sq).map (fun x : ℝ × ℝ => (a * cos x.1 - b * cos x.2) / D) := by
  obtain ⟨hmap, hae⟩ := lemma2 ha hb hD
  have hD0 : D ≠ 0 := by linarith
  have hg : Measurable (fun x : ℝ × ℝ => (a * cos x.1 - b * cos x.2) / D) := by fun_prop
  rw [Measure.map_congr (g := (fun x : ℝ × ℝ => (a * cos x.1 - b * cos x.2) / D) ∘ angles2 a b D)
      ?_, ← Measure.map_map hg (measurable_angles2 a b D), hmap, Measure.map_smul]
  · exact hg.aemeasurable
  filter_upwards [hae] with ω hω
  have h := offsets2_eq (D := D) ha hb ω hω
  simp only [offsets2, Prod.mk.injEq] at h
  have hp := nrmD_perp (pt 0 b ω.2 - pt (-D) a ω.1)
  simp only [Function.comp, ← h.1, ← h.2, nrm]
  unfold off
  simp only [Prod.fst_sub, Prod.snd_sub] at hp
  field_simp
  linear_combination hp

end Chords
