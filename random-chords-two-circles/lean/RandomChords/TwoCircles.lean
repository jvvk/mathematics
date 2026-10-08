import RandomChords.OneCircle

/-!
# Lemma 2: two circles

`A` uniform on the circle of radius `a` about `P = (-D, 0)`, `B` uniform on the circle of radius `b`
about `Q = (0, 0)`, with `a + b ≤ D` (disjoint interiors). The paper's proof, step by step:

* the offset equations give `D cos φ = a cos θ_A - b cos θ_B` (`D_cos_phi`), which fixes the normal
  angle `φ ∈ (0, π)` (`phi`);
* the four pairs on the line are at polar angles `(φ + εθ_A, φ + ηθ_B)` (`psi2`); differentiating,
  `∂φ/∂θ_A = u / g` and `∂φ/∂θ_B = -v / g` (`hasFDerivAt_phi`), with `g = D sin φ`, `u = a sin θ_A`,
  `v = b sin θ_B`;
* each determinant is `1 + εu/g - ηv/g` in absolute value (`det_psi2'`), which is the pair's gap
  over `g` and is non-negative because the chords are disjoint (`half_chords_le`, `jac_nonneg`);
* the four add to `4` (`sum_jac`): the half-chords cancel; with the density `1/(4π²)` of `(α, β)`
  this is the density `1/π²` of two independent uniform angles on `(0, π)` (`lemma2`).

Tangencies and coincident points are handled by the branch theorem: a branch's domain is where its
gap is positive, and the Jacobian vanishes elsewhere.
-/

open Real MeasureTheory Set
open scoped ENNReal
noncomputable section
namespace Chords

section
variable (a b D : ℝ)

/-- `cos φ = (a cos θ_A - b cos θ_B) / D` (the offset equations). -/
def wcos (x : ℝ × ℝ) : ℝ := (a * cos x.1 - b * cos x.2) / D
/-- The normal angle `φ ∈ (0, π)` of the line with angles `x = (θ_A, θ_B)`. -/
def phi (x : ℝ × ℝ) : ℝ := arccos (wcos a b D x)
/-- The gap `g = D sin φ` between the feet of the perpendiculars. -/
def gfeet (x : ℝ × ℝ) : ℝ := D * sin (phi a b D x)
end

variable {a b D : ℝ}

lemma cos_mem_Ioo {t : ℝ} (h : t ∈ Ioo 0 π) : cos t ∈ Ioo (-1) 1 := by
  constructor
  · rw [← cos_pi]; exact cos_lt_cos_of_nonneg_of_le_pi h.1.le le_rfl h.2
  · rw [← cos_zero]; exact cos_lt_cos_of_nonneg_of_le_pi le_rfl h.2.le h.1

lemma wcos_mem (ha : 0 < a) (hb : 0 < b) (hD : a + b ≤ D) {x : ℝ × ℝ} (hx : x ∈ sq) :
    wcos a b D x ∈ Ioo (-1) 1 := by
  obtain ⟨c1, c1'⟩ := cos_mem_Ioo hx.1
  obtain ⟨c2, c2'⟩ := cos_mem_Ioo hx.2
  have hD0 : 0 < D := by linarith
  unfold wcos
  constructor
  · rw [lt_div_iff₀ hD0]; nlinarith
  · rw [div_lt_iff₀ hD0]; nlinarith

lemma phi_mem (ha : 0 < a) (hb : 0 < b) (hD : a + b ≤ D) {x : ℝ × ℝ} (hx : x ∈ sq) :
    phi a b D x ∈ Ioo 0 π := by
  obtain ⟨h1, h2⟩ := wcos_mem ha hb hD hx
  exact ⟨arccos_pos.2 h2, arccos_lt_pi.2 h1⟩

lemma D_cos_phi (ha : 0 < a) (hb : 0 < b) (hD : a + b ≤ D) {x : ℝ × ℝ} (hx : x ∈ sq) :
    D * cos (phi a b D x) = a * cos x.1 - b * cos x.2 := by
  obtain ⟨h1, h2⟩ := wcos_mem ha hb hD hx
  have hD0 : D ≠ 0 := by linarith
  rw [phi, cos_arccos h1.le h2.le, wcos]
  field_simp

lemma gfeet_pos (ha : 0 < a) (hb : 0 < b) (hD : a + b ≤ D) {x : ℝ × ℝ} (hx : x ∈ sq) :
    0 < gfeet a b D x := by
  obtain ⟨h1, h2⟩ := phi_mem ha hb hD hx
  exact mul_pos (by linarith) (sin_pos_of_pos_of_lt_pi h1 h2)

/-- The four gaps are non-negative: `g ≥ u + v` (the chords are disjoint). -/
lemma half_chords_le (ha : 0 < a) (hb : 0 < b) (hD : a + b ≤ D) {x : ℝ × ℝ} (hx : x ∈ sq) :
    a * sin x.1 + b * sin x.2 ≤ gfeet a b D x := by
  have hg := gfeet_pos ha hb hD hx
  have hc := D_cos_phi ha hb hD hx
  have hs1 : 0 < sin x.1 := sin_pos_of_pos_of_lt_pi hx.1.1 hx.1.2
  have hs2 : 0 < sin x.2 := sin_pos_of_pos_of_lt_pi hx.2.1 hx.2.2
  have hg2 : gfeet a b D x ^ 2 = D ^ 2 - (a * cos x.1 - b * cos x.2) ^ 2 := by
    rw [← hc]; unfold gfeet
    have e3 := sin_sq_add_cos_sq (phi a b D x)
    linear_combination D ^ 2 * e3
  have hsq : (a * sin x.1 + b * sin x.2) ^ 2 ≤ gfeet a b D x ^ 2 := by
    have hcos : -1 ≤ cos (x.1 + x.2) := neg_one_le_cos _
    rw [cos_add] at hcos
    have e1 := sin_sq_add_cos_sq x.1
    have e2 := sin_sq_add_cos_sq x.2
    have hD2 : (a + b) ^ 2 ≤ D ^ 2 := pow_le_pow_left₀ (by positivity) hD 2
    have key : (a * sin x.1 + b * sin x.2) ^ 2 + (a * cos x.1 - b * cos x.2) ^ 2 =
        a ^ 2 + b ^ 2 - 2 * a * b * (cos x.1 * cos x.2 - sin x.1 * sin x.2) := by
      linear_combination a ^ 2 * e1 + b ^ 2 * e2
    rw [hg2]
    nlinarith [mul_le_mul_of_nonneg_left hcos (by positivity : (0 : ℝ) ≤ 2 * a * b)]
  exact (pow_le_pow_iff_left₀ (by positivity) hg.le two_ne_zero).1 hsq


section
variable (a b D : ℝ)
/-- `∂φ/∂θ_A = u / g` with `u = a sin θ_A`. -/
def c1 (x : ℝ × ℝ) : ℝ := a * sin x.1 / gfeet a b D x
/-- `∂φ/∂θ_B = -v / g` with `v = b sin θ_B`. -/
def c2 (x : ℝ × ℝ) : ℝ := -(b * sin x.2 / gfeet a b D x)

/-- The inverse branch `(θ_A, θ_B) ↦ (α, β) = (φ + εθ_A, φ + ηθ_B)`. -/
def psi2 (ε η : Bool) (x : ℝ × ℝ) : ℝ × ℝ :=
  (phi a b D x + sgnB ε * x.1, phi a b D x + sgnB η * x.2)

/-- Its derivative. -/
def psi2' (ε η : Bool) (x : ℝ × ℝ) : ℝ × ℝ →L[ℝ] ℝ × ℝ :=
  ((c1 a b D x + sgnB ε) • ContinuousLinearMap.fst ℝ ℝ ℝ + c2 a b D x • ContinuousLinearMap.snd ℝ ℝ ℝ).prod
    (c1 a b D x • ContinuousLinearMap.fst ℝ ℝ ℝ + (c2 a b D x + sgnB η) • ContinuousLinearMap.snd ℝ ℝ ℝ)

/-- The contribution of a branch: its gap divided by the feet-to-feet gap,
`1 + ε u / g - η v / g`. -/
def jac (ε η : Bool) (x : ℝ × ℝ) : ℝ := 1 + sgnB ε * c1 a b D x + sgnB η * c2 a b D x
end

lemma hasFDerivAt_phi (ha : 0 < a) (hb : 0 < b) (hD : a + b ≤ D) {x : ℝ × ℝ} (hx : x ∈ sq) :
    HasFDerivAt (phi a b D)
      (c1 a b D x • ContinuousLinearMap.fst ℝ ℝ ℝ + c2 a b D x • ContinuousLinearMap.snd ℝ ℝ ℝ) x := by
  obtain ⟨hw1, hw2⟩ := wcos_mem ha hb hD hx
  have hD0 : D ≠ 0 := by linarith
  have h1 : HasFDerivAt (fun x : ℝ × ℝ => cos x.1) (-sin x.1 • ContinuousLinearMap.fst ℝ ℝ ℝ) x :=
    (hasDerivAt_cos x.1).comp_hasFDerivAt x (hasFDerivAt_fst)
  have h2 : HasFDerivAt (fun x : ℝ × ℝ => cos x.2) (-sin x.2 • ContinuousLinearMap.snd ℝ ℝ ℝ) x :=
    (hasDerivAt_cos x.2).comp_hasFDerivAt x (hasFDerivAt_snd)
  have hw : HasFDerivAt (wcos a b D) ((-(a * sin x.1) / D) • ContinuousLinearMap.fst ℝ ℝ ℝ +
      (b * sin x.2 / D) • ContinuousLinearMap.snd ℝ ℝ ℝ) x := by
    have e : wcos a b D = fun x => D⁻¹ * (a * cos x.1 - b * cos x.2) := by
      funext y; simp [wcos, div_eq_inv_mul]
    rw [e]
    have := ((h1.const_mul a).sub (h2.const_mul b)).const_mul D⁻¹
    refine this.congr_fderiv ?_
    ext <;> simp <;> field_simp
  have harc := (hasDerivAt_arccos hw1.ne' hw2.ne).comp_hasFDerivAt x hw
  have hg : gfeet a b D x = D * √(1 - wcos a b D x ^ 2) := by rw [gfeet, phi, sin_arccos]
  have hsq : 0 < √(1 - wcos a b D x ^ 2) := by
    apply Real.sqrt_pos.2; nlinarith
  refine harc.congr_fderiv ?_
  ext <;> simp [c1, c2, hg] <;> field_simp

lemma hasFDerivAt_psi2 (ha : 0 < a) (hb : 0 < b) (hD : a + b ≤ D) (ε η : Bool) {x : ℝ × ℝ}
    (hx : x ∈ sq) : HasFDerivAt (psi2 a b D ε η) (psi2' a b D ε η x) x := by
  have hφ := hasFDerivAt_phi ha hb hD hx
  have := (hφ.add (hasFDerivAt_fst.const_mul (sgnB ε))).prodMk (hφ.add (hasFDerivAt_snd.const_mul (sgnB η)))
  refine this.congr_fderiv ?_
  ext <;> simp [psi2']

lemma det_psi2' (ε η : Bool) (x : ℝ × ℝ) :
    |(psi2' a b D ε η x).det| = |jac a b D ε η x| := by
  rw [psi2', det_two, jac]
  have h : (c1 a b D x + sgnB ε) * (c2 a b D x + sgnB η) - c2 a b D x * c1 a b D x =
      (sgnB ε * sgnB η) * (1 + sgnB ε * c1 a b D x + sgnB η * c2 a b D x) := by
    cases ε <;> cases η <;> simp only [sgnB] <;> norm_num <;> ring
  have h1 : |sgnB ε * sgnB η| = 1 := by cases ε <;> cases η <;> norm_num [sgnB]
  rw [h, abs_mul, h1, one_mul]

lemma jac_eq (ha : 0 < a) (hb : 0 < b) (hD : a + b ≤ D) (ε η : Bool) {x : ℝ × ℝ} (hx : x ∈ sq) :
    jac a b D ε η x =
      (gfeet a b D x + sgnB ε * (a * sin x.1) - sgnB η * (b * sin x.2)) / gfeet a b D x := by
  have hg := (gfeet_pos ha hb hD hx).ne'
  rw [jac, c1, c2]; field_simp; ring

lemma jac_nonneg (ha : 0 < a) (hb : 0 < b) (hD : a + b ≤ D) (ε η : Bool) {x : ℝ × ℝ}
    (hx : x ∈ sq) : 0 ≤ jac a b D ε η x := by
  rw [jac_eq ha hb hD ε η hx]
  have hg := gfeet_pos ha hb hD hx
  have hl := half_chords_le ha hb hD hx
  have hs1 : 0 < sin x.1 := sin_pos_of_pos_of_lt_pi hx.1.1 hx.1.2
  have hs2 : 0 < sin x.2 := sin_pos_of_pos_of_lt_pi hx.2.1 hx.2.2
  apply div_nonneg _ hg.le
  cases ε <;> cases η <;> simp [sgnB] <;> nlinarith [mul_pos ha hs1, mul_pos hb hs2]

/-- The four contributions add up to `4`: the half-chords cancel. -/
lemma sum_jac (x : ℝ × ℝ) :
    ∑ p : Bool × Bool, jac a b D p.1 p.2 x = 4 := by
  simp [Fintype.sum_prod_type, jac, sgnB]; ring

lemma cos_add_sgnB (φ t : ℝ) (ε : Bool) :
    cos (φ + sgnB ε * t) = cos φ * cos t - sgnB ε * (sin φ * sin t) := by
  cases ε <;> simp [sgnB, cos_add, cos_sub, ← sub_eq_add_neg]

lemma sin_add_sgnB (φ t : ℝ) (ε : Bool) :
    sin (φ + sgnB ε * t) = sin φ * cos t + sgnB ε * (cos φ * sin t) := by
  cases ε <;> simp [sgnB, sin_add, sin_sub, ← sub_eq_add_neg]

lemma cos_sgnB (t : ℝ) (ε : Bool) : cos (sgnB ε * t) = cos t := by cases ε <;> simp [sgnB]

/-- The domain of a branch: the angle pairs whose points `A, B` on that branch are distinct
(positive gap). -/
def dom2 (a b D : ℝ) (ε η : Bool) : Set (ℝ × ℝ) := {x | x ∈ sq ∧ 0 < jac a b D ε η x}

/-- On its domain, the branch `(φ + εθ_A, φ + ηθ_B)` gives back the angles `(θ_A, θ_B)`, and
`A ≠ B`. -/
lemma branch2 (ha : 0 < a) (hb : 0 < b) (hD : a + b ≤ D) (ε η : Bool) {x : ℝ × ℝ}
    (hx : x ∈ dom2 a b D ε η) :
    angles2 a b D (proj (psi2 a b D ε η x)) = x ∧
      pt (-D) a (proj (psi2 a b D ε η x)).1 ≠ pt 0 b (proj (psi2 a b D ε η x)).2 := by
  obtain ⟨hxs, hj⟩ := hx
  obtain ⟨hφ1, hφ2⟩ := phi_mem ha hb hD hxs
  have hsφ : 0 < sin (phi a b D x) := sin_pos_of_pos_of_lt_pi hφ1 hφ2
  have hc := D_cos_phi ha hb hD hxs
  have hgpos := gfeet_pos ha hb hD hxs
  set l := gfeet a b D x + sgnB ε * (a * sin x.1) - sgnB η * (b * sin x.2) with hl
  have hl0 : 0 < l := by
    rw [jac_eq ha hb hD ε η hxs] at hj
    exact (div_pos_iff_of_pos_right hgpos).1 hj
  have hd : pt 0 b (proj (psi2 a b D ε η x)).2 - pt (-D) a (proj (psi2 a b D ε η x)).1 =
      (l * sin (phi a b D x), -(l * cos (phi a b D x))) := by
    have e3 := sin_sq_add_cos_sq (phi a b D x)
    simp only [proj, psi2, pt, ccos_coe, csin_coe, cos_add_sgnB, sin_add_sgnB, hl, gfeet]
    refine Prod.ext ?_ ?_
    · simp only [Prod.fst_sub]
      linear_combination (cos (phi a b D x)) * hc - D * e3
    · simp only [Prod.snd_sub]
      linear_combination (sin (phi a b D x)) * hc
  have hm : nrm (pt (-D) a (proj (psi2 a b D ε η x)).1) (pt 0 b (proj (psi2 a b D ε η x)).2) =
      (cos (phi a b D x), sin (phi a b D x)) := by
    rw [nrm, hd, nrmD_eq hl0.ne' hsφ]
  refine ⟨?_, ?_⟩
  · unfold angles2
    rw [hm]
    have hA : (proj (psi2 a b D ε η x)).1 = ((phi a b D x + sgnB ε * x.1 : ℝ) : Ang) := rfl
    have hB : (proj (psi2 a b D ε η x)).2 = ((phi a b D x + sgnB η * x.2 : ℝ) : Ang) := rfl
    rw [hA, hB, off_pt _ _ _ _ ha.ne', off_pt _ _ _ _ hb.ne', add_sub_cancel_left,
      add_sub_cancel_left, cos_sgnB, cos_sgnB,
      arccos_cos hxs.1.1.le hxs.1.2.le, arccos_cos hxs.2.1.le hxs.2.2.le]
  · intro h
    rw [h, sub_self] at hd
    have h0 := congrArg Prod.fst hd
    simp only [Prod.fst_zero] at h0
    exact (mul_ne_zero hl0.ne' hsφ.ne') h0.symm

lemma measurable_c1 : Measurable (c1 a b D) := by
  unfold c1 gfeet phi wcos; fun_prop
lemma measurable_c2 : Measurable (c2 a b D) := by
  unfold c2 gfeet phi wcos; fun_prop
lemma measurable_jac (ε η : Bool) : Measurable (jac a b D ε η) := by
  unfold jac; exact (measurable_const.add (measurable_const.mul measurable_c1)).add
    (measurable_const.mul measurable_c2)

/-- **Lemma 2.** If the two discs have disjoint interiors (`a + b ≤ D`), the angles `θ_A, θ_B`
between the normal of `AB` and the radii to `A` and `B` are independent and uniform on `(0, π)`:
the law of `(θ_A, θ_B)` under `volume` on `Ang × Ang` is `4 • volume` on the square. Moreover
`A ≠ B` almost surely. -/
theorem lemma2 (ha : 0 < a) (hb : 0 < b) (hD : a + b ≤ D) :
    Measure.map (angles2 a b D) volume = (4 : ℝ≥0∞) • volume.restrict sq ∧
      ∀ᵐ ω ∂(volume : Measure (Ang × Ang)), pt (-D) a ω.1 ≠ pt 0 b ω.2 := by
  have key := map_eq_of_branches (ι := Bool × Bool) (angles2 a b D) (measurable_angles2 a b D)
    sq measurableSet_sq 4
    (fun p => psi2 a b D p.1 p.2) (fun p x => psi2' a b D p.1 p.2 x)
    (fun p => dom2 a b D p.1 p.2)
    (fun p => measurableSet_sq.inter (measurableSet_lt measurable_const (measurable_jac p.1 p.2)))
    (fun p => fun x hx => hx.1)
    (fun p => ((if p.1 then 0 else -π), (if p.2 then 0 else -π)))
    (by
      rintro ⟨ε, η⟩ x ⟨hxs, -⟩
      obtain ⟨hφ1, hφ2⟩ := phi_mem ha hb hD hxs
      obtain ⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩ := hxs
      simp only [psi2, box]
      cases ε <;> cases η <;> simp [sgnB] <;> constructor <;> constructor <;> linarith)
    (fun p x hx => (hasFDerivAt_psi2 ha hb hD p.1 p.2 hx.1).hasFDerivWithinAt)
    (fun p x hx => (branch2 ha hb hD p.1 p.2 hx).1)
    (by
      rintro ⟨ε, η⟩ ⟨ε', η'⟩ hij x hx _ h
      obtain ⟨hφ1, hφ2⟩ := phi_mem ha hb hD hx.1
      have hsφ := sin_pos_of_pos_of_lt_pi hφ1 hφ2
      obtain ⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩ := hx.1
      have hs1 := mul_pos hsφ (sin_pos_of_pos_of_lt_pi h1 h2)
      have hs2 := mul_pos hsφ (sin_pos_of_pos_of_lt_pi h3 h4)
      have hc1 := congrArg (fun ω : Ang × Ang => ccos ω.1) h
      have hc2 := congrArg (fun ω : Ang × Ang => ccos ω.2) h
      simp only [proj, psi2, ccos_coe, cos_add_sgnB] at hc1 hc2
      cases ε <;> cases η <;> cases ε' <;> cases η' <;> simp only [sgnB] at hc1 hc2 <;>
        first | exact hij rfl | (norm_num at hc1 hc2; linarith))
    (fun p x => ENNReal.ofReal (jac a b D p.1 p.2 x))
    (fun p => ENNReal.measurable_ofReal.comp (measurable_jac p.1 p.2))
    (by
      rintro ⟨ε, η⟩ x hx
      simp only
      rw [det_psi2', abs_of_nonneg (jac_nonneg ha hb hD ε η hx.1)])
    (by
      rintro ⟨ε, η⟩ x ⟨hxs, hxd⟩
      simp only [dom2, mem_ofPred_eq, not_and, not_lt] at hxd
      exact ENNReal.ofReal_eq_zero.2 (hxd hxs))
    (by
      intro x hx
      rw [← ENNReal.ofReal_sum_of_nonneg (fun p _ => jac_nonneg ha hb hD p.1 p.2 hx), sum_jac]
      norm_num)
    four_mul_volume_sq
  refine ⟨key.1, ?_⟩
  filter_upwards [key.2] with ω hω
  obtain ⟨p, x, hx, rfl⟩ := hω
  exact (branch2 ha hb hD p.1 p.2 hx).2

end Chords
