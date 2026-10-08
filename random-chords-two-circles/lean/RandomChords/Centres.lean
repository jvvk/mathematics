import RandomChords.TwoCircles
import RandomChords.Moments

/-!
# Theorem 4: which centres see the two lines alike

The circles have radii `a` about `P = (q - D, 0)` and `b` about `Q = (q, 0)`, `a + b ≤ D`, and
`O = (q + o, 0)` is a point of the line of centres (`o = μ D` in the paper's notation, so `o ≥ 0`
puts `O` beyond `Q`, away from `P`, at distance `|QO| = |o|`). `dAB` is the distance from `O` to the
line `AB`, `dBC` the distance from `O` to the chord line `BC`.

* `dAB_eq`, `dBC_eq`: the projection identity (T): `d(O, AB) = |(1 + μ) b x_B - μ a x_A|` and
  `d(O, BC) = |b x_B - μ D cos φ|`, written as `|w₁ cos θ₁ + w₂ cos θ₂|` in the angles of Lemmas 1, 2;
* `law_dAB`, `law_dBC`: so both laws are weighted arcsine sums (Lemmas 1 and 2);
* `theorem4`: they agree exactly when `O = Q`, or the circles touch and `|QO| = b (a + b) / a` with
  `O` beyond `Q`; the common law is that of `|b cos U - |QO| cos V|` (`law_dBC'`).
-/

open Real MeasureTheory Set
open scoped ENNReal

noncomputable section

namespace Chords

variable {a b D : ℝ}

/-! ### Plane facts -/

lemma len_pos {d : ℝ × ℝ} (hd : d ≠ 0) : 0 < len d := by
  unfold len
  apply Real.sqrt_pos.2
  rcases d with ⟨d1, d2⟩
  by_contra h
  push Not at h
  have h1 : d1 = 0 := by nlinarith [sq_nonneg d1, sq_nonneg d2]
  have h2 : d2 = 0 := by nlinarith [sq_nonneg d1, sq_nonneg d2]
  exact hd (by simp [h1, h2])

lemma len_sq (d : ℝ × ℝ) : len d ^ 2 = d.1 ^ 2 + d.2 ^ 2 := by
  unfold len; rw [sq_sqrt (by positivity)]

lemma sgn_sq (d : ℝ × ℝ) : sgn d ^ 2 = 1 := by unfold sgn; split_ifs <;> norm_num

lemma abs_sgn (d : ℝ × ℝ) : |sgn d| = 1 := by unfold sgn; split_ifs <;> norm_num

/-- The normal is a unit vector. -/
lemma nrmD_unit {d : ℝ × ℝ} (hd : d ≠ 0) : (nrmD d).1 ^ 2 + (nrmD d).2 ^ 2 = 1 := by
  have hL := (len_pos hd).ne'
  unfold nrmD
  simp only [div_pow, mul_pow, neg_sq, sgn_sq, one_mul]
  rw [← add_div, div_eq_one_iff_eq (pow_ne_zero 2 hL), len_sq]; ring

/-- The normal is perpendicular to the direction. -/
lemma nrmD_perp (d : ℝ × ℝ) : (nrmD d).1 * d.1 + (nrmD d).2 * d.2 = 0 := by
  unfold nrmD; ring

/-- The distance from `O` to the line `XY` is `|m · (O - X)|`. -/
lemma lineDist_eq (O X Y : ℝ × ℝ) (h : X ≠ Y) :
    lineDist O X Y = |(nrm X Y).1 * (O.1 - X.1) + (nrm X Y).2 * (O.2 - X.2)| := by
  have hd : Y - X ≠ 0 := sub_ne_zero.2 (Ne.symm h)
  have hL := len_pos hd
  unfold lineDist nrm nrmD
  rw [show sgn (Y - X) * -(Y - X).2 / len (Y - X) * (O.1 - X.1) +
      sgn (Y - X) * (Y - X).1 / len (Y - X) * (O.2 - X.2) =
      sgn (Y - X) * ((Y.1 - X.1) * (O.2 - X.2) - (Y.2 - X.2) * (O.1 - X.1)) / len (Y - X) by
    simp only [Prod.fst_sub, Prod.snd_sub]; ring,
    abs_div, abs_mul, abs_sgn, one_mul, abs_of_pos hL]

/-- A unit normal's offset from a circle through the point is at most `1` in size. -/
lemma abs_off_le {m : ℝ × ℝ} (hm : m.1 ^ 2 + m.2 ^ 2 = 1) (c r : ℝ) (hr : 0 < r) (α : Ang) :
    |off m (pt c r α) (c, 0) r| ≤ 1 := by
  unfold off pt
  simp only [add_sub_cancel_left, sub_zero]
  have hcs : ccos α ^ 2 + csin α ^ 2 = 1 := by
    induction α using QuotientAddGroup.induction_on with
    | H x => simp [cos_sq_add_sin_sq]
  have key : (m.1 * ccos α + m.2 * csin α) ^ 2 ≤ 1 := by
    have hprod : (m.1 ^ 2 + m.2 ^ 2) * (ccos α ^ 2 + csin α ^ 2) = 1 := by rw [hm, hcs, one_mul]
    nlinarith [sq_nonneg (m.1 * csin α - m.2 * ccos α)]
  have h1 := (sq_le_one_iff_abs_le_one _).1 key
  rw [show m.1 * (r * ccos α) + m.2 * (r * csin α) = r * (m.1 * ccos α + m.2 * csin α) by ring,
    mul_div_cancel_left₀ _ hr.ne']
  exact h1

lemma abs_off_le' {m : ℝ × ℝ} (hm : m.1 ^ 2 + m.2 ^ 2 = 1) (c r : ℝ) (hr : 0 < r) (α : Ang) :
    -1 ≤ off m (pt c r α) (c, 0) r ∧ off m (pt c r α) (c, 0) r ≤ 1 :=
  abs_le.1 (abs_off_le hm c r hr α)

lemma abs_fst_le {m : ℝ × ℝ} (hm : m.1 ^ 2 + m.2 ^ 2 = 1) : -1 ≤ m.1 ∧ m.1 ≤ 1 := by
  constructor <;> nlinarith [sq_nonneg m.2, sq_nonneg (m.1 + 1), sq_nonneg (m.1 - 1)]

/-- Translating along the axis moves points of circles and keeps distances. -/
lemma pt_add (c q r : ℝ) (α : Ang) : pt (q + c) r α = pt c r α + (q, 0) := by
  unfold pt; ext <;> simp <;> ring

lemma lineDist_add (O X Y v : ℝ × ℝ) : lineDist (O + v) (X + v) (Y + v) = lineDist O X Y := by
  unfold lineDist; simp only [Prod.fst_add, Prod.snd_add, add_sub_add_right_eq_sub]

/-! ### The distances and the projection identity (T) -/

/-- The distance from `O = (q + o, 0)` to the line `AB`. -/
def dAB (a b D q o : ℝ) (ω : Ang × Ang) : ℝ := lineDist (q + o, 0) (pt (q - D) a ω.1) (pt q b ω.2)

/-- The distance from `O = (q + o, 0)` to the chord line `BC` of the second circle. -/
def dBC (b q o : ℝ) (ω : Ang × Ang) : ℝ := lineDist (q + o, 0) (pt q b ω.1) (pt q b ω.2)

lemma dAB_shift (q o : ℝ) (ω : Ang × Ang) :
    dAB a b D q o ω = lineDist (o, 0) (pt (-D) a ω.1) (pt 0 b ω.2) := by
  have h1 : ((q + o, 0) : ℝ × ℝ) = (o, 0) + (q, 0) := by ext <;> simp; ring
  rw [dAB, h1, show q - D = q + -D by ring, pt_add, ← add_zero q, pt_add, add_zero,
    lineDist_add]

lemma dBC_shift (q o : ℝ) (ω : Ang × Ang) :
    dBC b q o ω = lineDist (o, 0) (pt 0 b ω.1) (pt 0 b ω.2) := by
  have h1 : ((q + o, 0) : ℝ × ℝ) = (o, 0) + (q, 0) := by ext <;> simp; ring
  rw [dBC, h1, ← add_zero q, pt_add, pt_add, add_zero, lineDist_add]

/-- **(T) for `AB`.** `d(O, AB) = |μ a x_A - (1 + μ) b x_B|` with `μ = o / D`. -/
lemma dAB_eq (ha : 0 < a) (hb : 0 < b) (hD : a + b ≤ D) (q o : ℝ) (ω : Ang × Ang)
    (hω : pt (-D) a ω.1 ≠ pt 0 b ω.2) :
    dAB a b D q o ω = wsum (o / D * a, -((1 + o / D) * b)) (angles2 a b D ω) := by
  have hD0 : D ≠ 0 := by linarith
  set A := pt (-D) a ω.1 with hA
  set B := pt 0 b ω.2 with hB
  have hm := nrmD_unit (sub_ne_zero.2 (Ne.symm hω))
  have hperp := nrmD_perp (B - A)
  rw [dAB_shift, lineDist_eq _ _ _ hω, wsum, angles2]
  rw [← hA, ← hB]
  obtain ⟨hA1, hA2⟩ := abs_off_le' hm (-D) a ha ω.1
  obtain ⟨hB1, hB2⟩ := abs_off_le' hm 0 b hb ω.2
  rw [nrm, ← hA, ← hB] at *
  simp only at hA1 hA2 hB1 hB2 ⊢
  rw [cos_arccos hA1 hA2, cos_arccos hB1 hB2]
  congr 1
  unfold off
  simp only [Prod.fst_sub, Prod.snd_sub] at hperp ⊢
  field_simp
  linear_combination (o + D) * hperp

/-- **(T) for `BC`.** `d(O, BC) = |o cos φ - b x_B|`. -/
lemma dBC_eq (hb : 0 < b) (q o : ℝ) (ω : Ang × Ang) (hω : pt 0 b ω.1 ≠ pt 0 b ω.2) :
    dBC b q o ω = wsum (o, -b) (angles1 b ω) := by
  set B := pt 0 b ω.1 with hB
  set C := pt 0 b ω.2 with hC
  have hm := nrmD_unit (sub_ne_zero.2 (Ne.symm hω))
  rw [dBC_shift, lineDist_eq _ _ _ hω, wsum, angles1]
  rw [← hB, ← hC]
  obtain ⟨hB1, hB2⟩ := abs_off_le' hm 0 b hb ω.1
  obtain ⟨hm1, hm2⟩ := abs_fst_le hm
  rw [nrm, ← hB, ← hC] at *
  simp only at hB1 hB2 ⊢
  rw [cos_arccos hm1 hm2, cos_arccos hB1 hB2]
  congr 1
  unfold off
  field_simp
  ring

/-! ### The two laws -/

lemma law_dAB (ha : 0 < a) (hb : 0 < b) (hD : a + b ≤ D) (q o : ℝ) :
    Measure.map (dAB a b D q o) volume =
      (4 : ℝ≥0∞) • lawW (o / D * a, -((1 + o / D) * b)) := by
  obtain ⟨hmap, hae⟩ := lemma2 ha hb hD
  rw [Measure.map_congr (g := wsum (o / D * a, -((1 + o / D) * b)) ∘ angles2 a b D)
    (by filter_upwards [hae] with ω hω using dAB_eq ha hb hD q o ω hω),
    ← Measure.map_map (continuous_wsum _).measurable (measurable_angles2 a b D), hmap,
    Measure.map_smul, lawW]
  exact (continuous_wsum _).aemeasurable

lemma law_dBC (hb : 0 < b) (q o : ℝ) :
    Measure.map (dBC b q o) volume = (4 : ℝ≥0∞) • lawW (o, -b) := by
  obtain ⟨hmap, hae⟩ := lemma1 b hb
  rw [Measure.map_congr (g := wsum (o, -b) ∘ angles1 b)
    (by filter_upwards [hae] with ω hω using dBC_eq hb q o ω hω),
    ← Measure.map_map (continuous_wsum _).measurable (measurable_angles1 b), hmap,
    Measure.map_smul, lawW]
  exact (continuous_wsum _).aemeasurable

/-- The law of `d(O, BC)` is that of `|b cos U - |QO| cos V|`. -/
lemma law_dBC' (hb : 0 < b) (q o : ℝ) :
    Measure.map (dBC b q o) volume = (4 : ℝ≥0∞) • lawW (b, -|o|) := by
  rw [law_dBC hb, ← lawW_abs (b, -|o|), ← lawW_abs (o, -b)]
  simp only [abs_neg, abs_abs, abs_of_pos hb]
  rw [← lawW_swap]

lemma smul_four_inj {μ ν : Measure ℝ} : (4 : ℝ≥0∞) • μ = (4 : ℝ≥0∞) • ν ↔ μ = ν := by
  constructor
  · intro h
    ext s hs
    have := congrArg (fun m : Measure ℝ => m s) h
    simp only [Measure.smul_apply, smul_eq_mul] at this
    exact (ENNReal.mul_right_inj (by norm_num) (by norm_num)).1 this
  · intro h; rw [h]

/-- The weight comparison of the proof of Theorem 4. -/
lemma weights_iff (ha : 0 < a) (hb : 0 < b) (hD : a + b ≤ D) (o : ℝ) :
    ((|o / D * a| = |o| ∧ |-((1 + o / D) * b)| = |-b|) ∨
      (|o / D * a| = |-b| ∧ |-((1 + o / D) * b)| = |o|)) ↔
      o = 0 ∨ (D = a + b ∧ o = b * (a + b) / a) := by
  have hD0 : 0 < D := by linarith
  simp only [abs_neg, abs_mul, abs_div, abs_of_pos ha, abs_of_pos hb, abs_of_pos hD0]
  constructor
  · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
    · -- `|μ| a = |μ| D` forces `μ = 0`, since `a < D`
      left
      by_contra ho
      have hpos : 0 < |o| := abs_pos.2 ho
      field_simp at h1
      have : a = D := by nlinarith
      linarith
    · -- `|μ| a = b` and `|1 + μ| b = |μ| D`
      right
      have hoa : |o| * a = b * D := by field_simp at h1; linarith
      have h1' : |1 + o / D| = |o| / b := by field_simp at h2 ⊢; linarith
      have htri : |1 + o / D| ≤ 1 + |o| / D := by
        calc |1 + o / D| ≤ |1| + |o / D| := abs_add_le _ _
          _ = 1 + |o| / D := by rw [abs_one, abs_div, abs_of_pos hD0]
      rw [h1'] at htri
      -- `|o| / b = D / a ≥ (a + b) / a = 1 + |o| / D`
      have ho_eq : |o| = b * D / a := by field_simp; linarith
      rw [ho_eq] at htri
      have hDeq : D = a + b := by
        have : D / a ≤ 1 + b / a := by
          have e1 : b * D / a / b = D / a := by field_simp
          have e2 : b * D / a / D = b / a := by field_simp
          rwa [e1, e2] at htri
        rw [div_le_iff₀ ha] at this
        have : D ≤ a + b := by
          have := this; field_simp at this; linarith
        linarith
      refine ⟨hDeq, ?_⟩
      -- the triangle inequality is an equality, so `o ≥ 0`
      rcases le_or_gt 0 o with hoo | hoo
      · rw [abs_of_nonneg hoo] at ho_eq; rw [ho_eq, hDeq]
      · exfalso
        rw [abs_of_neg hoo] at ho_eq
        have hlt : |1 + o / D| < 1 + |o| / D := by
          rw [abs_of_neg hoo]
          have hq : o / D < 0 := div_neg_of_neg_of_pos hoo hD0
          rw [abs_lt]; constructor <;>
            · have : -o / D = -(o / D) := by ring
              rw [this]; linarith
        rw [h1'] at hlt
        rw [abs_of_neg hoo, ho_eq] at hlt
        have e1 : b * D / a / b = D / a := by field_simp
        have e2 : b * D / a / D = b / a := by field_simp
        rw [e1, e2, hDeq] at hlt
        have : (a + b) / a = 1 + b / a := by field_simp
        linarith
  · rintro (h | ⟨h1, h2⟩)
    · left; subst h; simp
    · right
      subst h1
      have hab : 0 < a + b := by linarith
      have ho : 0 ≤ o := by rw [h2]; positivity
      rw [abs_of_nonneg ho, h2]
      constructor
      · field_simp
      · rw [abs_of_pos (by positivity)]; field_simp

/-- **Theorem 4.** For circles with disjoint interiors and a point `O = (q + o, 0)` of the line of
centres, `d(O, AB)` and `d(O, BC)` have the same law if and only if `O = Q` (`o = 0`), or the circles
touch (`D = a + b`) and `O` lies beyond `Q`, away from `P`, with `|QO| = b (a + b) / a`. -/
theorem theorem4 (ha : 0 < a) (hb : 0 < b) (hD : a + b ≤ D) (q o : ℝ) :
    Measure.map (dAB a b D q o) volume = Measure.map (dBC b q o) volume ↔
      o = 0 ∨ (D = a + b ∧ o = b * (a + b) / a) := by
  rw [law_dAB ha hb hD, law_dBC hb, smul_four_inj, lemma3]
  exact weights_iff ha hb hD o

end Chords
