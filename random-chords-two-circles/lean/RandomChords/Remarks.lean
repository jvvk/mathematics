import RandomChords.HitProb

/-!
# Remarks: disjointness is needed; an exact test off the axis

* `concentric`: for concentric circles of different radii the offsets satisfy `a x_A = b x_B`, so the
  angles `(θ_A, θ_B)` are not uniform on the square: Lemma 2 fails without disjointness.
* `offaxis_moment` (2): for `O = (h, k)` off the line of centres,
  `E d(O, AB)² - E d(O, BC)² = (Δ (k² - h²) + 2 b² D h) / (2 D²)`, `Δ = D² - a² - b²`, from
  `T_AB = b Y - (h/D)(a X - b Y) - k √(1 - (a X - b Y)²/D²)`, the symmetry `(X, Y) ↦ (-X, -Y)`
  (`(θ_A, θ_B) ↦ (π - θ_A, π - θ_B)`), and `E X² = E Y² = 1/2`, `E XY = 0`.
* `offaxis_necessary`, `offaxis_perp`, `offaxis_example`: equality of the laws forces
  `Δ (k² - h²) + 2 b² D h = 0`; a nonzero perpendicular displacement from either centre of
  Theorem 4 destroys equality; moving `(3, 0)` to `(3, 0.3)` in Figure 1 adds exactly `0.02`.
-/

open Real MeasureTheory Set
open scoped ENNReal

noncomputable section

namespace Chords

variable {a b D : ℝ}

/-! ### Concentric circles -/

/-- For concentric circles (`D = 0`) the offsets satisfy `a x_A = b x_B`. -/
lemma concentric_offsets (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (ω : Ang × Ang) :
    a * off (nrm (pt (-0) a ω.1) (pt 0 b ω.2)) (pt (-0) a ω.1) (-0, 0) a =
      b * off (nrm (pt (-0) a ω.1) (pt 0 b ω.2)) (pt 0 b ω.2) (0, 0) b := by
  have hp := nrmD_perp (pt 0 b ω.2 - pt (-0) a ω.1)
  unfold off nrm at *
  simp only [neg_zero, sub_zero, Prod.fst_sub, Prod.snd_sub] at hp ⊢
  field_simp
  linear_combination -hp

lemma pt_ne_of_radius {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (hab : a ≠ b) (α β : Ang) :
    pt (-0) a α ≠ pt 0 b β := by
  intro h
  have h1 := congrArg Prod.fst h
  have h2 := congrArg Prod.snd h
  simp only [pt, neg_zero, zero_add] at h1 h2
  have hcs : ∀ γ : Ang, ccos γ ^ 2 + csin γ ^ 2 = 1 := fun γ => by
    induction γ using QuotientAddGroup.induction_on with
    | H x => simp [cos_sq_add_sin_sq]
  have : a ^ 2 = b ^ 2 := by
    have e1 := hcs α; have e2 := hcs β
    linear_combination (-a ^ 2) * e1 + b ^ 2 * e2 + (a * ccos α + b * ccos β) * h1 +
      (a * csin α + b * csin β) * h2
  exact hab ((sq_eq_sq₀ ha.le hb.le).1 this)

/-- **Disjointness is needed.** For concentric circles of radii `a ≠ b`, the law of `(θ_A, θ_B)` is
not uniform: the box `(0, π/3) × (2π/3, π)` has positive area but probability zero. -/
theorem concentric (ha : 0 < a) (hb : 0 < b) (hab : a ≠ b) :
    Measure.map (angles2 a b 0) volume ≠ (4 : ℝ≥0∞) • volume.restrict sq := by
  intro h
  set E : Set (ℝ × ℝ) := Ioo 0 (π / 3) ×ˢ Ioo (2 * π / 3) π with hE
  have hEm : MeasurableSet E := measurableSet_Ioo.prod measurableSet_Ioo
  have hzero : Measure.map (angles2 a b 0) volume E = 0 := by
    rw [Measure.map_apply (measurable_angles2 a b 0) hEm]
    convert measure_empty (μ := (volume : Measure (Ang × Ang)))
    ext ω
    simp only [mem_preimage, mem_empty_iff_false, iff_false]
    rintro ⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩
    have hne := pt_ne_of_radius ha hb hab ω.1 ω.2
    have hm := nrmD_unit (sub_ne_zero.2 (Ne.symm hne))
    obtain ⟨hA1, hA2⟩ := abs_off_le' hm (-0) a ha ω.1
    obtain ⟨hB1, hB2⟩ := abs_off_le' hm 0 b hb ω.2
    have hrel := concentric_offsets a b ha hb ω
    simp only [angles2] at h1 h2 h3 h4
    rw [nrm] at *
    set xA := off (nrmD (pt 0 b ω.2 - pt (-0) a ω.1)) (pt (-0) a ω.1) (-0, 0) a
    set xB := off (nrmD (pt 0 b ω.2 - pt (-0) a ω.1)) (pt 0 b ω.2) (0, 0) b
    -- `θ_A < π/3` gives `x_A > 1/2`, `θ_B > 2π/3` gives `x_B < -1/2`
    have hxA : 1 / 2 < xA := by
      have := cos_lt_cos_of_nonneg_of_le_pi (arccos_nonneg xA) (by linarith [pi_pos]) h2
      rwa [cos_arccos hA1 hA2, cos_pi_div_three] at this
    have hxB : xB < -1 / 2 := by
      have := cos_lt_cos_of_nonneg_of_le_pi (by linarith [pi_pos]) (arccos_le_pi xB) h3
      rw [cos_arccos hB1 hB2, show 2 * π / 3 = π - π / 3 by ring, cos_pi_sub,
        cos_pi_div_three] at this
      linarith
    nlinarith
  have hpos : (0 : ℝ≥0∞) < ((4 : ℝ≥0∞) • volume.restrict sq) E := by
    rw [Measure.smul_apply, smul_eq_mul, Measure.restrict_apply hEm]
    have hsub : E ∩ sq = E := by
      apply inter_eq_left.2
      rintro p ⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩
      exact ⟨⟨h1, by linarith [pi_pos]⟩, ⟨by linarith [pi_pos], h4⟩⟩
    rw [hsub]
    refine ENNReal.mul_pos (by norm_num) ?_
    exact (isOpen_Ioo.prod isOpen_Ioo).measure_pos volume
      ⟨(π / 6, 5 * π / 6), ⟨by constructor <;> linarith [pi_pos], by constructor <;> linarith [pi_pos]⟩⟩ |>.ne'
  rw [h] at hzero
  exact hpos.ne' hzero

/-! ### Off the axis -/

/-- The distance from `O = (h, k)` to `AB`, and to the chord `BC`. -/
def dOff (a b D h k : ℝ) (ω : Ang × Ang) : ℝ := lineDist (h, k) (pt (-D) a ω.1) (pt 0 b ω.2)
def dOffC (b h k : ℝ) (ω : Ang × Ang) : ℝ := lineDist (h, k) (pt 0 b ω.1) (pt 0 b ω.2)

lemma nrmD_snd_nonneg (d : ℝ × ℝ) : 0 ≤ (nrmD d).2 := by
  unfold nrmD sgn len
  apply div_nonneg _ (Real.sqrt_nonneg _)
  split_ifs with h
  · linarith
  · push Not at h; nlinarith

lemma snd_eq_sqrt {m : ℝ × ℝ} (hm : m.1 ^ 2 + m.2 ^ 2 = 1) (h2 : 0 ≤ m.2) :
    m.2 = √(1 - m.1 ^ 2) := by
  rw [show 1 - m.1 ^ 2 = m.2 ^ 2 by linarith, Real.sqrt_sq h2]

lemma lineDist_eq' (O X Y : ℝ × ℝ) (h : X ≠ Y) :
    lineDist O X Y = |(nrm X Y).1 * (O.1 - Y.1) + (nrm X Y).2 * (O.2 - Y.2)| := by
  rw [lineDist_eq _ _ _ h]
  have hp := nrmD_perp (Y - X)
  rw [nrm]; simp only [Prod.fst_sub, Prod.snd_sub] at hp
  congr 1; linear_combination hp

/-- `T_AB` as a function of the angles. -/
def G1 (a b D h k : ℝ) (x : ℝ × ℝ) : ℝ :=
  (h * ((a * cos x.1 - b * cos x.2) / D) + k * √(1 - ((a * cos x.1 - b * cos x.2) / D) ^ 2)
    - b * cos x.2) ^ 2

/-- `T_BC` as a function of the angles. -/
def G2 (b h k : ℝ) (x : ℝ × ℝ) : ℝ := (h * cos x.1 + k * sin x.1 - b * cos x.2) ^ 2

lemma dOff_sq (ha : 0 < a) (hb : 0 < b) (hD : a + b ≤ D) (h k : ℝ) (ω : Ang × Ang)
    (hω : pt (-D) a ω.1 ≠ pt 0 b ω.2) :
    dOff a b D h k ω ^ 2 = G1 a b D h k (angles2 a b D ω) := by
  have hD0 : D ≠ 0 := by linarith
  have hm := nrmD_unit (sub_ne_zero.2 (Ne.symm hω))
  have h2 := nrmD_snd_nonneg (pt 0 b ω.2 - pt (-D) a ω.1)
  have hp := nrmD_perp (pt 0 b ω.2 - pt (-D) a ω.1)
  obtain ⟨hA1, hA2⟩ := abs_off_le' hm (-D) a ha ω.1
  obtain ⟨hB1, hB2⟩ := abs_off_le' hm 0 b hb ω.2
  rw [dOff, lineDist_eq' _ _ _ hω, sq_abs, G1, angles2]
  simp only
  rw [nrm] at *
  rw [cos_arccos hA1 hA2, cos_arccos hB1 hB2]
  set m := nrmD (pt 0 b ω.2 - pt (-D) a ω.1)
  have hm1 : m.1 = (a * off m (pt (-D) a ω.1) (-D, 0) a - b * off m (pt 0 b ω.2) (0, 0) b) / D := by
    unfold off
    simp only [Prod.fst_sub, Prod.snd_sub] at hp
    field_simp
    linear_combination hp
  rw [← hm1, ← snd_eq_sqrt hm h2]
  congr 1
  unfold off
  field_simp
  ring

lemma dOffC_sq (hb : 0 < b) (h k : ℝ) (ω : Ang × Ang) (hω : pt 0 b ω.1 ≠ pt 0 b ω.2) :
    dOffC b h k ω ^ 2 = G2 b h k (angles1 b ω) := by
  have hm := nrmD_unit (sub_ne_zero.2 (Ne.symm hω))
  have h2 := nrmD_snd_nonneg (pt 0 b ω.2 - pt 0 b ω.1)
  have hp := nrmD_perp (pt 0 b ω.2 - pt 0 b ω.1)
  obtain ⟨hB1, hB2⟩ := abs_off_le' hm 0 b hb ω.1
  obtain ⟨hm1, hm2⟩ := abs_fst_le hm
  rw [dOffC, lineDist_eq' _ _ _ hω, sq_abs, G2, angles1]
  simp only
  rw [nrm] at *
  rw [cos_arccos hm1 hm2, sin_arccos, ← snd_eq_sqrt hm h2, cos_arccos hB1 hB2]
  congr 1
  unfold off
  simp only [Prod.fst_sub, Prod.snd_sub] at hp
  field_simp
  linear_combination -hp

/-! ### Integrals over the square -/

lemma integral_sin_sq_Ioo : ∫ u in Ioo 0 π, sin u ^ 2 = π / 2 := by
  rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le pi_pos.le, integral_sin_sq]
  simp

/-- A function odd under `(u, v) ↦ (π - u, v)` integrates to zero on the square. -/
lemma integral_odd1 (f : ℝ × ℝ → ℝ) (hf : Continuous f) (hodd : ∀ x, f (π - x.1, x.2) = -f x) :
    ∫ x in sq, f x = 0 := by
  have h := integral_map (μ := volume.restrict sq) mp_reflect1.measurable.aemeasurable
    (f := f) hf.aestronglyMeasurable
  rw [mp_reflect1.map_eq] at h
  simp only [hodd, integral_neg] at h
  linarith

/-- A function odd under `(u, v) ↦ (u, π - v)` integrates to zero on the square. -/
lemma integral_odd2 (f : ℝ × ℝ → ℝ) (hf : Continuous f) (hodd : ∀ x, f (x.1, π - x.2) = -f x) :
    ∫ x in sq, f x = 0 := by
  have h := integral_map (μ := volume.restrict sq) mp_reflect2.measurable.aemeasurable
    (f := f) hf.aestronglyMeasurable
  rw [mp_reflect2.map_eq] at h
  simp only [hodd, integral_neg] at h
  linarith

lemma mp_reflect12 : MeasurePreserving (fun p : ℝ × ℝ => (π - p.1, π - p.2))
    (volume.restrict sq) (volume.restrict sq) :=
  mp_reflect1.comp mp_reflect2

/-- A function odd under `(u, v) ↦ (π - u, π - v)` integrates to zero on the square. -/
lemma integral_odd12 (f : ℝ × ℝ → ℝ) (hf : Continuous f)
    (hodd : ∀ x, f (π - x.1, π - x.2) = -f x) : ∫ x in sq, f x = 0 := by
  have h := integral_map (μ := volume.restrict sq) mp_reflect12.measurable.aemeasurable
    (f := f) hf.aestronglyMeasurable
  rw [mp_reflect12.map_eq] at h
  simp only [hodd, integral_neg] at h
  linarith

lemma integrable_cont (f : ℝ × ℝ → ℝ) (hf : Continuous f) (C : ℝ) (hC : ∀ x, |f x| ≤ C) :
    Integrable f (volume.restrict sq) := integrable_sq f hf C hC

lemma integral_cos1_sq : ∫ x in sq, cos x.1 ^ 2 = π ^ 2 / 2 := by
  have := integral_prod_mul (μ := volume.restrict (Ioo (0 : ℝ) π)) (ν := volume.restrict (Ioo (0 : ℝ) π))
    (fun u => cos u ^ 2) (fun _ => (1 : ℝ))
  rw [← restrict_sq] at this
  simp only [mul_one] at this
  rw [this, integral_cos_sq_Ioo, integral_one_Ioo]; ring

lemma integral_cos2_sq : ∫ x in sq, cos x.2 ^ 2 = π ^ 2 / 2 := by
  have := integral_prod_mul (μ := volume.restrict (Ioo (0 : ℝ) π)) (ν := volume.restrict (Ioo (0 : ℝ) π))
    (fun _ => (1 : ℝ)) (fun v => cos v ^ 2)
  rw [← restrict_sq] at this
  simp only [one_mul] at this
  rw [this, integral_cos_sq_Ioo, integral_one_Ioo]; ring

lemma integral_sin1_sq : ∫ x in sq, sin x.1 ^ 2 = π ^ 2 / 2 := by
  have := integral_prod_mul (μ := volume.restrict (Ioo (0 : ℝ) π)) (ν := volume.restrict (Ioo (0 : ℝ) π))
    (fun u => sin u ^ 2) (fun _ => (1 : ℝ))
  rw [← restrict_sq] at this
  simp only [mul_one] at this
  rw [this, integral_sin_sq_Ioo, integral_one_Ioo]; ring

lemma integral_one_sq : ∫ _ in sq, (1 : ℝ) = π ^ 2 := by
  rw [setIntegral_const, smul_eq_mul, mul_one, Measure.real, volume_sq,
    ← ENNReal.ofReal_mul pi_pos.le, ENNReal.toReal_ofReal (by positivity)]; ring

/-- `∫ (T_BC)² = π² (h² + k² + b²) / 2`. -/
lemma integral_G2 (b h k : ℝ) : ∫ x in sq, G2 b h k x = π ^ 2 * (h ^ 2 + k ^ 2 + b ^ 2) / 2 := by
  have e : ∀ x : ℝ × ℝ, G2 b h k x = h ^ 2 * cos x.1 ^ 2 + k ^ 2 * sin x.1 ^ 2 + b ^ 2 * cos x.2 ^ 2
      + (2 * h * k * (cos x.1 * sin x.1) + (-2 * b * cos x.2) * (h * cos x.1 + k * sin x.1)) := by
    intro x; unfold G2; ring
  simp_rw [e]
  have hb1 : ∀ x : ℝ × ℝ, |cos x.1 ^ 2| ≤ 1 := fun x => by
    rw [abs_of_nonneg (sq_nonneg _)]; exact cos_sq_le_one _
  have i1 : Integrable (fun x : ℝ × ℝ => h ^ 2 * cos x.1 ^ 2) (volume.restrict sq) :=
    (integrable_cont _ (by fun_prop) 1 hb1).const_mul _
  have i2 : Integrable (fun x : ℝ × ℝ => k ^ 2 * sin x.1 ^ 2) (volume.restrict sq) :=
    (integrable_cont _ (by fun_prop) 1 (fun x => by
      rw [abs_of_nonneg (sq_nonneg _)]; exact sin_sq_le_one _)).const_mul _
  have i3 : Integrable (fun x : ℝ × ℝ => b ^ 2 * cos x.2 ^ 2) (volume.restrict sq) :=
    (integrable_cont _ (by fun_prop) 1 (fun x => by
      rw [abs_of_nonneg (sq_nonneg _)]; exact cos_sq_le_one _)).const_mul _
  have i4 : Integrable (fun x : ℝ × ℝ => 2 * h * k * (cos x.1 * sin x.1)) (volume.restrict sq) :=
    (integrable_cont _ (by fun_prop) 1 (fun x => by
      rw [abs_mul]; exact (mul_le_mul (abs_cos_le_one _) (abs_sin_le_one _) (abs_nonneg _)
        zero_le_one).trans (by norm_num))).const_mul _
  have i5 : Integrable (fun x : ℝ × ℝ => (-2 * b * cos x.2) * (h * cos x.1 + k * sin x.1))
      (volume.restrict sq) :=
    integrable_cont _ (by fun_prop) (2 * |b| * (|h| + |k|)) (fun x => by
      rw [abs_mul]
      have e1 : |-2 * b * cos x.2| ≤ 2 * |b| := by
        rw [abs_mul, abs_mul]; simp only [abs_neg, abs_two]
        nlinarith [abs_cos_le_one x.2, abs_nonneg b]
      have e2 : |h * cos x.1 + k * sin x.1| ≤ |h| + |k| := by
        refine (abs_add_le _ _).trans ?_
        rw [abs_mul, abs_mul]
        nlinarith [abs_cos_le_one x.1, abs_sin_le_one x.1, abs_nonneg h, abs_nonneg k]
      exact mul_le_mul e1 e2 (abs_nonneg _) (by positivity))
  have z4 : ∫ x in sq, 2 * h * k * (cos x.1 * sin x.1) = 0 :=
    integral_odd1 _ (by fun_prop) (fun x => by simp [cos_pi_sub, sin_pi_sub])
  have z5 : ∫ x in sq, (-2 * b * cos x.2) * (h * cos x.1 + k * sin x.1) = 0 :=
    integral_odd2 _ (by fun_prop) (fun x => by simp [cos_pi_sub])
  have i12 : Integrable (fun x : ℝ × ℝ => h ^ 2 * cos x.1 ^ 2 + k ^ 2 * sin x.1 ^ 2)
      (volume.restrict sq) := i1.add i2
  have i123 : Integrable (fun x : ℝ × ℝ => h ^ 2 * cos x.1 ^ 2 + k ^ 2 * sin x.1 ^ 2 +
      b ^ 2 * cos x.2 ^ 2) (volume.restrict sq) := i12.add i3
  have i45 : Integrable (fun x : ℝ × ℝ => 2 * h * k * (cos x.1 * sin x.1) +
      (-2 * b * cos x.2) * (h * cos x.1 + k * sin x.1)) (volume.restrict sq) := i4.add i5
  rw [integral_add i123 i45, integral_add i12 i3, integral_add i1 i2, integral_add i4 i5, z4, z5, integral_const_mul, integral_const_mul,
    integral_const_mul, integral_cos1_sq, integral_sin1_sq, integral_cos2_sq]
  ring

lemma integral_cos12 : ∫ x in sq, cos x.1 * cos x.2 = 0 :=
  integral_odd1 _ (by fun_prop) (fun x => by simp [cos_pi_sub])

lemma continuous_G1 (a b D h k : ℝ) : Continuous (G1 a b D h k) := by unfold G1; fun_prop

/-- `∫ (T_AB)²` over the square. -/
lemma integral_G1 (ha : 0 < a) (hb : 0 < b) (hD : a + b ≤ D) (h k : ℝ) :
    ∫ x in sq, G1 a b D h k x =
      π ^ 2 / 2 * ((h ^ 2 - k ^ 2) * (a ^ 2 + b ^ 2) / D ^ 2 + 2 * h * b ^ 2 / D + b ^ 2) +
        π ^ 2 * k ^ 2 := by
  have hD0 : D ≠ 0 := by linarith
  set α := (h ^ 2 - k ^ 2) * a ^ 2 / D ^ 2
  set β := -2 * (h ^ 2 - k ^ 2) * a * b / D ^ 2 - 2 * h * b * a / D
  set γ := (h ^ 2 - k ^ 2) * b ^ 2 / D ^ 2 + 2 * h * b ^ 2 / D + b ^ 2
  set cr : ℝ × ℝ → ℝ := fun x => 2 * k * √(1 - ((a * cos x.1 - b * cos x.2) / D) ^ 2) *
    (h * ((a * cos x.1 - b * cos x.2) / D) - b * cos x.2) with hcr
  have hsplit : ∀ x ∈ sq, G1 a b D h k x =
      α * cos x.1 ^ 2 + β * (cos x.1 * cos x.2) + γ * cos x.2 ^ 2 + k ^ 2 * 1 + cr x := by
    intro x hx
    have hw := wcos_mem ha hb hD hx
    unfold wcos at hw
    have hS : √(1 - ((a * cos x.1 - b * cos x.2) / D) ^ 2) ^ 2 =
        1 - ((a * cos x.1 - b * cos x.2) / D) ^ 2 := sq_sqrt (by nlinarith [hw.1, hw.2])
    unfold G1
    simp only [hcr, α, β, γ]
    linear_combination k ^ 2 * hS
  rw [setIntegral_congr_fun measurableSet_sq hsplit]
  have hzc : ∫ x in sq, cr x = 0 := by
    refine integral_odd12 _ (by simp only [hcr]; fun_prop) (fun x => ?_)
    simp only [hcr, cos_pi_sub]
    rw [show (a * -cos x.1 - b * -cos x.2) / D = -((a * cos x.1 - b * cos x.2) / D) by ring, neg_sq]
    ring
  have ib : ∀ (f : ℝ × ℝ → ℝ), Continuous f → (∀ x, |f x| ≤ 1) → Integrable f (volume.restrict sq) :=
    fun f hf hC => integrable_cont f hf 1 hC
  have i1 : Integrable (fun x : ℝ × ℝ => α * cos x.1 ^ 2) (volume.restrict sq) :=
    (ib _ (by fun_prop) (fun x => by
      rw [abs_of_nonneg (sq_nonneg _)]; exact cos_sq_le_one _)).const_mul _
  have i2 : Integrable (fun x : ℝ × ℝ => β * (cos x.1 * cos x.2)) (volume.restrict sq) :=
    (ib _ (by fun_prop) (fun x => by
      rw [abs_mul]; exact (mul_le_mul (abs_cos_le_one _) (abs_cos_le_one _) (abs_nonneg _)
        zero_le_one).trans (by norm_num))).const_mul _
  have i3 : Integrable (fun x : ℝ × ℝ => γ * cos x.2 ^ 2) (volume.restrict sq) :=
    (ib _ (by fun_prop) (fun x => by
      rw [abs_of_nonneg (sq_nonneg _)]; exact cos_sq_le_one _)).const_mul _
  have i4 : Integrable (fun _ : ℝ × ℝ => k ^ 2 * 1) (volume.restrict sq) := integrable_const _
  have i5 : Integrable cr (volume.restrict sq) := by
    refine integrable_cont _ (by simp only [hcr]; fun_prop)
      (2 * |k| * (|h| * ((a + b) / |D|) + b)) (fun x => ?_)
    simp only [hcr]
    have hs : √(1 - ((a * cos x.1 - b * cos x.2) / D) ^ 2) ≤ 1 := by
      rw [Real.sqrt_le_one]; nlinarith [sq_nonneg ((a * cos x.1 - b * cos x.2) / D)]
    have hc : |(a * cos x.1 - b * cos x.2) / D| ≤ (a + b) / |D| := by
      rw [abs_div]
      apply div_le_div_of_nonneg_right _ (abs_nonneg _)
      refine (abs_sub _ _).trans ?_
      rw [abs_mul, abs_mul, abs_of_pos ha, abs_of_pos hb]
      nlinarith [abs_cos_le_one x.1, abs_cos_le_one x.2]
    have hY : |b * cos x.2| ≤ b := by
      rw [abs_mul, abs_of_pos hb]; nlinarith [abs_cos_le_one x.2]
    rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)]
    simp only [abs_two]
    have h1 : |h * ((a * cos x.1 - b * cos x.2) / D) - b * cos x.2| ≤ |h| * ((a + b) / |D|) + b := by
      refine (abs_sub _ _).trans ?_
      rw [abs_mul]
      nlinarith [abs_nonneg h]
    have h2 : 0 ≤ |h * ((a * cos x.1 - b * cos x.2) / D) - b * cos x.2| := abs_nonneg _
    calc 2 * |k| * √(1 - ((a * cos x.1 - b * cos x.2) / D) ^ 2) *
          |h * ((a * cos x.1 - b * cos x.2) / D) - b * cos x.2|
        ≤ 2 * |k| * 1 * (|h| * ((a + b) / |D|) + b) := by gcongr
      _ = 2 * |k| * (|h| * ((a + b) / |D|) + b) := by ring
  have i12 : Integrable (fun x : ℝ × ℝ => α * cos x.1 ^ 2 + β * (cos x.1 * cos x.2))
      (volume.restrict sq) := i1.add i2
  have i123 : Integrable (fun x : ℝ × ℝ => α * cos x.1 ^ 2 + β * (cos x.1 * cos x.2) +
      γ * cos x.2 ^ 2) (volume.restrict sq) := i12.add i3
  have i1234 : Integrable (fun x : ℝ × ℝ => α * cos x.1 ^ 2 + β * (cos x.1 * cos x.2) +
      γ * cos x.2 ^ 2 + k ^ 2 * 1) (volume.restrict sq) := i123.add i4
  rw [integral_add i1234 i5, integral_add i123 i4, integral_add i12 i3, integral_add i1 i2, hzc,
    integral_const_mul, integral_const_mul, integral_const_mul, integral_const_mul,
    integral_cos1_sq, integral_cos12, integral_cos2_sq, integral_one_sq]
  simp only [α, γ]
  field_simp
  ring

lemma measurable_dOff (a b D h k : ℝ) : Measurable (dOff a b D h k) := by
  unfold dOff lineDist
  exact (Continuous.measurable (by fun_prop)).div
    (measurable_len.comp (Continuous.measurable (by fun_prop)))

lemma measurable_dOffC (b h k : ℝ) : Measurable (dOffC b h k) := by
  unfold dOffC lineDist
  exact (Continuous.measurable (by fun_prop)).div
    (measurable_len.comp (Continuous.measurable (by fun_prop)))

lemma integral_dOff_sq (ha : 0 < a) (hb : 0 < b) (hD : a + b ≤ D) (h k : ℝ) :
    ∫ ω, dOff a b D h k ω ^ 2 = 4 * ∫ x in sq, G1 a b D h k x := by
  obtain ⟨hmap, hae⟩ := lemma2 ha hb hD
  rw [integral_congr_ae (g := fun ω => G1 a b D h k (angles2 a b D ω))
      (by filter_upwards [hae] with ω hω using dOff_sq ha hb hD h k ω hω),
    ← integral_map (measurable_angles2 a b D).aemeasurable
      (continuous_G1 a b D h k).aestronglyMeasurable, hmap, integral_smul_measure]
  simp

lemma integral_dOffC_sq (hb : 0 < b) (h k : ℝ) :
    ∫ ω, dOffC b h k ω ^ 2 = 4 * ∫ x in sq, G2 b h k x := by
  obtain ⟨hmap, hae⟩ := lemma1 b hb
  rw [integral_congr_ae (g := fun ω => G2 b h k (angles1 b ω))
      (by filter_upwards [hae] with ω hω using dOffC_sq hb h k ω hω),
    ← integral_map (measurable_angles1 b).aemeasurable
      (by unfold G2; fun_prop : Continuous (G2 b h k)).aestronglyMeasurable, hmap,
    integral_smul_measure]
  simp

/-- **The off-axis test (2).** For `O = (h, k)`, the mean squared distances to `AB` and to `BC`
(means over the uniform law, mass `4π²`) differ by `(Δ (k² - h²) + 2 b² D h) / (2 D²)`,
`Δ = D² - a² - b²`. -/
theorem offaxis_moment (ha : 0 < a) (hb : 0 < b) (hD : a + b ≤ D) (h k : ℝ) :
    (∫ ω, dOff a b D h k ω ^ 2) / (4 * π ^ 2) - (∫ ω, dOffC b h k ω ^ 2) / (4 * π ^ 2) =
      ((D ^ 2 - a ^ 2 - b ^ 2) * (k ^ 2 - h ^ 2) + 2 * b ^ 2 * D * h) / (2 * D ^ 2) := by
  have hD0 : D ≠ 0 := by linarith
  rw [integral_dOff_sq ha hb hD, integral_dOffC_sq hb, integral_G1 ha hb hD, integral_G2]
  field_simp
  ring

lemma delta_pos (ha : 0 < a) (hb : 0 < b) (hD : a + b ≤ D) : 0 < D ^ 2 - a ^ 2 - b ^ 2 := by
  nlinarith [mul_pos ha hb]

/-- **Equality off the axis needs** `h² - k² = 2 b² D h / Δ`. -/
theorem offaxis_necessary (ha : 0 < a) (hb : 0 < b) (hD : a + b ≤ D) (h k : ℝ)
    (heq : Measure.map (dOff a b D h k) volume = Measure.map (dOffC b h k) volume) :
    h ^ 2 - k ^ 2 = 2 * b ^ 2 * D * h / (D ^ 2 - a ^ 2 - b ^ 2) := by
  have hD0 : D ≠ 0 := by linarith
  have hΔ := delta_pos ha hb hD
  have e : ∫ ω, dOff a b D h k ω ^ 2 = ∫ ω, dOffC b h k ω ^ 2 := by
    have h1 := integral_map (μ := (volume : Measure (Ang × Ang)))
      (measurable_dOff a b D h k).aemeasurable (f := fun x : ℝ => x ^ 2)
      (by fun_prop : Continuous fun x : ℝ => x ^ 2).aestronglyMeasurable
    have h2 := integral_map (μ := (volume : Measure (Ang × Ang)))
      (measurable_dOffC b h k).aemeasurable (f := fun x : ℝ => x ^ 2)
      (by fun_prop : Continuous fun x : ℝ => x ^ 2).aestronglyMeasurable
    rw [← h1, ← h2, heq]
  have hm := offaxis_moment ha hb hD h k
  rw [e, sub_self] at hm
  have hnum : (D ^ 2 - a ^ 2 - b ^ 2) * (k ^ 2 - h ^ 2) + 2 * b ^ 2 * D * h = 0 := by
    have := hm.symm
    rwa [div_eq_zero_iff, or_iff_left (by positivity)] at this
  field_simp
  linarith

/-- **A perpendicular displacement destroys equality**: moving either centre of Theorem 4 off the
axis by `k ≠ 0` makes the two laws differ. -/
theorem offaxis_perp (ha : 0 < a) (hb : 0 < b) (hD : a + b ≤ D) {h k : ℝ} (hk : k ≠ 0)
    (hc : h = 0 ∨ (D = a + b ∧ h = b * (a + b) / a)) :
    Measure.map (dOff a b D h k) volume ≠ Measure.map (dOffC b h k) volume := by
  intro heq
  have hΔ := delta_pos ha hb hD
  have hn := offaxis_necessary ha hb hD h k heq
  rw [eq_div_iff hΔ.ne'] at hn
  have hk2 : 0 < k ^ 2 := by positivity
  rcases hc with rfl | ⟨rfl, rfl⟩
  · nlinarith
  · field_simp at hn
    nlinarith [mul_pos ha hb, mul_pos hΔ hk2, pow_pos ha 3]

/-- **The example.** Moving the successful centre of Figure 1 (`a = 1/2`, `b = 1`, `D = 3/2`,
`O = (3, 0)`) to `(3, 0.3)` makes the mean squared distance to `AB` exceed that to `BC` by `0.02`. -/
theorem offaxis_example :
    (∫ ω, dOff (1 / 2) 1 (3 / 2) 3 (3 / 10) ω ^ 2) / (4 * π ^ 2) -
      (∫ ω, dOffC 1 3 (3 / 10) ω ^ 2) / (4 * π ^ 2) = 1 / 50 := by
  rw [offaxis_moment (by norm_num) (by norm_num) (by norm_num)]
  norm_num

end Chords
