import LeanProofs.Phyllotaxis.FirstOrder

/-!
# Existence of the apex family (non-vacuity of the first-order lemmas)

`FirstOrder.lean` computes derivatives of any differentiable family of configurations that keeps the
stated tangencies. Here the implicit function theorem supplies such a family:

* `apex_exists`: if the moving disks `A` and `C` are `C¹` in `c` and a disk at `q0` touches both at
  `c = 0` with non-parallel contact normals, there is a unique `C¹` branch `Q(c)`, `Q(0) = q0`,
  touching
  both for all small `c` (diameters `b0 + c (hs x + hc y)`).
* `rhombic_family_exists`, `triangle_family_exists`: for every rhombic notch (`|U| = |D| = b0`,
  `U ∦ D`)
  and every triangle base (`|U| = b0`) there are families satisfying every hypothesis of
  `FirstOrder.rhombic_step` and `FirstOrder.triangle_step`. So those lemmas are not vacuous, and
  they
  apply to the geometric stacking step (the unique branch).
-/

namespace Phyllotaxis.Apex

open Filter Topology Phyllotaxis.FirstOrder

/-- Tangency defects of a disk centred at `p.2` against `A` and `C`, at rate `p.1`. -/
noncomputable def defect (b0 hs hc : ℝ) (ax ay cx cy : ℝ → ℝ) (p : ℝ × (ℝ × ℝ)) : ℝ × ℝ :=
  ((p.2.1 - ax p.1) ^ 2 + (p.2.2 - ay p.1) ^ 2 -
      (b0 + p.1 * (hs * (ax p.1 + p.2.1) + hc * (ay p.1 + p.2.2)) / 2) ^ 2,
    (cx p.1 - p.2.1) ^ 2 + (cy p.1 - p.2.2) ^ 2 -
      (b0 + p.1 * (hs * (p.2.1 + cx p.1) + hc * (p.2.2 + cy p.1)) / 2) ^ 2)

theorem defect_contDiffAt {b0 hs hc : ℝ} {ax ay cx cy : ℝ → ℝ} {q0 : ℝ × ℝ}
    (hax : ContDiffAt ℝ 1 ax 0) (hay : ContDiffAt ℝ 1 ay 0)
    (hcx : ContDiffAt ℝ 1 cx 0) (hcy : ContDiffAt ℝ 1 cy 0) :
    ContDiffAt ℝ 1 (defect b0 hs hc ax ay cx cy) (0, q0) := by
  have h1 : ContDiffAt ℝ 1 (fun p : ℝ × (ℝ × ℝ) => ax p.1) (0, q0) :=
    ContDiffAt.comp (g := ax) (0, q0) hax contDiffAt_fst
  have h2 : ContDiffAt ℝ 1 (fun p : ℝ × (ℝ × ℝ) => ay p.1) (0, q0) :=
    ContDiffAt.comp (g := ay) (0, q0) hay contDiffAt_fst
  have h3 : ContDiffAt ℝ 1 (fun p : ℝ × (ℝ × ℝ) => cx p.1) (0, q0) :=
    ContDiffAt.comp (g := cx) (0, q0) hcx contDiffAt_fst
  have h4 : ContDiffAt ℝ 1 (fun p : ℝ × (ℝ × ℝ) => cy p.1) (0, q0) :=
    ContDiffAt.comp (g := cy) (0, q0) hcy contDiffAt_fst
  have hf : ContDiffAt ℝ 1 (fun p : ℝ × (ℝ × ℝ) => p.1) (0, q0) := contDiffAt_fst
  have hq1 : ContDiffAt ℝ 1 (fun p : ℝ × (ℝ × ℝ) => p.2.1) (0, q0) :=
    contDiffAt_fst.comp _ contDiffAt_snd
  have hq2 : ContDiffAt ℝ 1 (fun p : ℝ × (ℝ × ℝ) => p.2.2) (0, q0) :=
    contDiffAt_snd.comp _ contDiffAt_snd
  unfold defect
  apply ContDiffAt.prodMk
  · exact (((hq1.sub h1).pow 2).add ((hq2.sub h2).pow 2)).sub
      ((contDiffAt_const.add ((hf.mul ((contDiffAt_const.mul (h1.add hq1)).add
        (contDiffAt_const.mul (h2.add hq2)))).div_const 2)).pow 2)
  · exact (((h3.sub hq1).pow 2).add ((h4.sub hq2).pow 2)).sub
      ((contDiffAt_const.add ((hf.mul ((contDiffAt_const.mul (hq1.add h3)).add
        (contDiffAt_const.mul (hq2.add h4)))).div_const 2)).pow 2)

/-- The partial derivative in the position, at `c = 0`: `v ↦ (2 (q0 - A)·v, -2 (C - q0)·v)`. -/
theorem defect_partial {b0 hs hc : ℝ} {ax ay cx cy : ℝ → ℝ} {q0 : ℝ × ℝ}
    {L : ℝ × (ℝ × ℝ) →L[ℝ] ℝ × ℝ} (hL : HasFDerivAt (defect b0 hs hc ax ay cx cy) L (0, q0))
    (v : ℝ × ℝ) :
    L (0, v) = (2 * (q0.1 - ax 0) * v.1 + 2 * (q0.2 - ay 0) * v.2,
      -(2 * (cx 0 - q0.1) * v.1) - 2 * (cy 0 - q0.2) * v.2) := by
  let γ : ℝ → ℝ × (ℝ × ℝ) := fun t => (0, q0 + t • v)
  have hγ : HasDerivAt γ (0, v) 0 := by
    have := (hasDerivAt_const (0 : ℝ) (0 : ℝ)).prodMk
      ((hasDerivAt_id (0 : ℝ)).smul_const v |>.const_add q0)
    simpa [γ] using this
  have hγ0 : γ 0 = (0, q0) := by simp [γ]
  have h1 : HasDerivAt (defect b0 hs hc ax ay cx cy ∘ γ) (L (0, v)) 0 := by
    rw [← hγ0] at hL
    exact hL.comp_hasDerivAt 0 hγ
  have hfun : defect b0 hs hc ax ay cx cy ∘ γ = fun t =>
      ((q0.1 + t * v.1 - ax 0) ^ 2 + (q0.2 + t * v.2 - ay 0) ^ 2 - b0 ^ 2,
        (cx 0 - (q0.1 + t * v.1)) ^ 2 + (cy 0 - (q0.2 + t * v.2)) ^ 2 - b0 ^ 2) := by
    funext t
    simp [defect, γ]
  have h2 : HasDerivAt (fun t : ℝ =>
      ((q0.1 + t * v.1 - ax 0) ^ 2 + (q0.2 + t * v.2 - ay 0) ^ 2 - b0 ^ 2,
        (cx 0 - (q0.1 + t * v.1)) ^ 2 + (cy 0 - (q0.2 + t * v.2)) ^ 2 - b0 ^ 2))
      (2 * (q0.1 - ax 0) * v.1 + 2 * (q0.2 - ay 0) * v.2,
        -(2 * (cx 0 - q0.1) * v.1) - 2 * (cy 0 - q0.2) * v.2) 0 := by
    have hx : HasDerivAt (fun t : ℝ => q0.1 + t * v.1) v.1 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).mul_const v.1).const_add q0.1
    have hy : HasDerivAt (fun t : ℝ => q0.2 + t * v.2) v.2 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).mul_const v.2).const_add q0.2
    have e1 := (((hx.sub_const (ax 0)).pow 2).add ((hy.sub_const (ay 0)).pow 2)).sub_const (b0 ^ 2)
    have e2 := (((hx.const_sub (cx 0)).pow 2).add ((hy.const_sub (cy 0)).pow 2)).sub_const (b0 ^ 2)
    convert e1.prodMk e2 using 1
    simp
    ring
  rw [hfun] at h1
  exact h1.unique h2

/-- **Apex family.** Implicit function theorem for the two tangency conditions. -/
theorem apex_exists {b0 hs hc : ℝ} {ax ay cx cy : ℝ → ℝ} {q0 : ℝ × ℝ}
    (hax : ContDiffAt ℝ 1 ax 0) (hay : ContDiffAt ℝ 1 ay 0)
    (hcx : ContDiffAt ℝ 1 cx 0) (hcy : ContDiffAt ℝ 1 cy 0)
    (hA : (q0.1 - ax 0) ^ 2 + (q0.2 - ay 0) ^ 2 = b0 ^ 2)
    (hC : (cx 0 - q0.1) ^ 2 + (cy 0 - q0.2) ^ 2 = b0 ^ 2)
    (hT : (q0.1 - ax 0) * (q0.2 - cy 0) - (q0.2 - ay 0) * (q0.1 - cx 0) ≠ 0) :
    ∃ ψ : ℝ → ℝ × ℝ, ∃ ψ' : ℝ × ℝ, ψ 0 = q0 ∧ HasDerivAt ψ ψ' 0 ∧
      (∀ᶠ c in 𝓝 0, defect b0 hs hc ax ay cx cy (c, ψ c) = 0) ∧
      (∀ᶠ p in 𝓝 ((0 : ℝ), q0), defect b0 hs hc ax ay cx cy p = 0 → ψ p.1 = p.2) := by
  set f := defect b0 hs hc ax ay cx cy
  have hcd : ContDiffAt ℝ 1 f (0, q0) := defect_contDiffAt hax hay hcx hcy
  have hs := hcd.hasStrictFDerivAt one_ne_zero
  set L := fderiv ℝ f (0, q0)
  have hf0 : f (0, q0) = 0 := by
    simp only [f, defect, zero_mul, zero_div, add_zero]
    rw [hA, hC]
    simp
  -- the partial derivative in `q` is injective, hence invertible
  set M := L ∘L ContinuousLinearMap.inr ℝ ℝ (ℝ × ℝ)
  have hM : ∀ v, M v = (2 * (q0.1 - ax 0) * v.1 + 2 * (q0.2 - ay 0) * v.2,
      -(2 * (cx 0 - q0.1) * v.1) - 2 * (cy 0 - q0.2) * v.2) := fun v =>
    defect_partial hs.hasFDerivAt v
  have hinj : Function.Injective M := by
    intro v w hvw
    rw [hM v, hM w] at hvw
    have e1 := congrArg Prod.fst hvw
    have e2 := congrArg Prod.snd hvw
    simp only at e1 e2
    have hv1 : v.1 = w.1 := by
      apply mul_left_cancel₀ hT
      linear_combination ((q0.2 - cy 0) / 2) * e1 - ((q0.2 - ay 0) / 2) * e2
    have hv2 : v.2 = w.2 := by
      apply mul_left_cancel₀ hT
      linear_combination (-(q0.1 - cx 0) / 2) * e1 + ((q0.1 - ax 0) / 2) * e2
    exact Prod.ext hv1 hv2
  have hMi : M.IsInvertible :=
    ⟨(LinearEquiv.ofInjectiveEndo (M : (ℝ × ℝ) →ₗ[ℝ] (ℝ × ℝ)) hinj).toContinuousLinearEquiv,
      by ext <;> rfl⟩
  refine ⟨hs.implicitFunctionOfProdDomain hMi, _, ?_,
    (hs.hasStrictFDerivAt_implicitFunctionOfProdDomain hMi).hasFDerivAt.hasDerivAt, ?_, ?_⟩
  · have := (hs.eventually_apply_eq_iff_implicitFunctionOfProdDomain hMi).self_of_nhds
    exact this.1 rfl
  · have := hs.eventually_apply_implicitFunctionOfProdDomain hMi
    simpa [hf0] using this
  · filter_upwards [hs.eventually_apply_eq_iff_implicitFunctionOfProdDomain hMi] with p hp h0
    exact hp.1 (by rw [h0, hf0])

/-- The apex family as a moving disk (`Mov`), touching `A` and `C` for all small `c`. -/
theorem apex_mov {b0 hs hc : ℝ} (A C : Mov) {q0 : ℝ × ℝ}
    (hax : ContDiffAt ℝ 1 A.x 0) (hay : ContDiffAt ℝ 1 A.y 0)
    (hcx : ContDiffAt ℝ 1 C.x 0) (hcy : ContDiffAt ℝ 1 C.y 0)
    (hA : (q0.1 - A.x 0) ^ 2 + (q0.2 - A.y 0) ^ 2 = b0 ^ 2)
    (hC : (C.x 0 - q0.1) ^ 2 + (C.y 0 - q0.2) ^ 2 = b0 ^ 2)
    (hT : (q0.1 - A.x 0) * (q0.2 - C.y 0) - (q0.2 - A.y 0) * (q0.1 - C.x 0) ≠ 0) :
    ∃ Q : Mov, Q.x 0 = q0.1 ∧ Q.y 0 = q0.2 ∧ Tan b0 hs hc A Q ∧ Tan b0 hs hc Q C := by
  obtain ⟨ψ, ψ', h0, hd, hev, -⟩ := apex_exists (hs := hs) (hc := hc) hax hay hcx hcy hA hC hT
  refine ⟨⟨fun c => (ψ c).1, fun c => (ψ c).2, ψ'.1, ψ'.2, hd.fst, hd.snd⟩,
    by simp [h0], by simp [h0], ?_, ?_⟩
  · filter_upwards [hev] with c hc'
    have := congrArg Prod.fst hc'
    simp only [defect, Prod.fst_zero] at this
    linarith
  · filter_upwards [hev] with c hc'
    have := congrArg Prod.snd hc'
    simp only [defect, Prod.snd_zero] at this
    linarith

/-! ## Non-vacuity -/

/-- A disk that does not move. -/
def still (a b : ℝ) : Mov :=
  ⟨fun _ => a, fun _ => b, 0, 0, hasDerivAt_const _ _, hasDerivAt_const _ _⟩

/-- A `C¹` motion, with its derivative at `0` taken as the velocity. -/
noncomputable def ofContDiff (x y : ℝ → ℝ) (hx : ContDiffAt ℝ 1 x 0) (hy : ContDiffAt ℝ 1 y 0) :
    Mov :=
  ⟨x, y, deriv x 0, deriv y 0, (hx.differentiableAt one_ne_zero).hasDerivAt,
    (hy.differentiableAt one_ne_zero).hasDerivAt⟩

theorem pos_eq {P : Mov} {a b : ℝ} (hx : P.x 0 = a) (hy : P.y 0 = b) : P.pos 0 = ⟨a, b⟩ := by
  apply Complex.ext <;> simp [Mov.pos, hx, hy]

/-- **Lemma 3 is not vacuous.** Every triangle base `U` with `|U| = b0` carries a family satisfying
all
hypotheses of `FirstOrder.triangle_step`. -/
theorem triangle_family_exists {b0 ux uy : ℝ} (hb : 0 < b0) (hU : ux ^ 2 + uy ^ 2 = b0 ^ 2) :
    ∃ B C Q : Mov, Tan b0 0 1 B C ∧ Tan b0 0 1 B Q ∧ Tan b0 0 1 Q C ∧
      Q.pos 0 = B.pos 0 + ω * (C.pos 0 - B.pos 0) ∧ C.pos 0 - B.pos 0 = ⟨ux, uy⟩ := by
  have h3 : √3 * √3 = 3 := Real.mul_self_sqrt (by norm_num)
  set B := still 0 (-uy / 2)
  set C := still ux (uy / 2)
  have hBC : Tan b0 0 1 B C := by
    refine Eventually.of_forall fun c => ?_
    simp only [B, C, still]
    linear_combination hU
  obtain ⟨Q, hqx, hqy, hBQ, hQC⟩ := apex_mov (b0 := b0) (hs := 0) (hc := 1) B C
    (q0 := (ux / 2 - √3 / 2 * uy, √3 / 2 * ux)) contDiffAt_const contDiffAt_const
    contDiffAt_const contDiffAt_const
    (by simp only [B, still]; linear_combination (1 / 4 * ux ^ 2 + 1 / 4 * uy ^ 2) * h3 + hU)
    (by simp only [C, still]; linear_combination (1 / 4 * ux ^ 2 + 1 / 4 * uy ^ 2) * h3 + hU)
    (by
      simp only [B, C, still]
      have : (ux / 2 - √3 / 2 * uy - 0) * (√3 / 2 * ux - uy / 2) -
          (√3 / 2 * ux - -uy / 2) * (ux / 2 - √3 / 2 * uy - ux) = √3 / 2 * b0 ^ 2 := by
        linear_combination (√3 / 2) * hU + (-(1 / 2) * ux * uy + 1 / 2 * ux * uy) * h3
      rw [this]
      positivity)
  refine ⟨B, C, Q, hBC, hBQ, hQC, ?_, ?_⟩
  · rw [pos_eq hqx hqy]
    apply Complex.ext <;> simp [Mov.pos, B, C, still, ω] <;> ring
  · apply Complex.ext <;> simp [Mov.pos, B, C, still]
    ring

/-- Length of the moving side `B -U-> C` when `B` is fixed at height `yB`:
`L (1 - c u_y/(2 b0)) = b0 + c yB`. -/
noncomputable def sideLen (b0 uy yB c : ℝ) : ℝ := (b0 + c * yB) / (1 - c * (uy / (2 * b0)))

theorem sideLen_contDiffAt (b0 uy yB : ℝ) : ContDiffAt ℝ 1 (sideLen b0 uy yB) 0 := by
  unfold sideLen
  exact (contDiffAt_const.add (contDiffAt_id.mul contDiffAt_const)).div
    (contDiffAt_const.sub (contDiffAt_id.mul contDiffAt_const)) (by simp)

/-- **Lemma 1 is not vacuous.** Every rhombic notch (`|U| = |D| = b0`, `U ∦ D`) carries a family
satisfying all hypotheses of `FirstOrder.rhombic_step`: `A`, `B` fixed with `y_A + y_B = 0`, `C`
moving
along `U` so that `B` and `C` stay tangent, and `Q` the apex branch. -/
theorem rhombic_family_exists {b0 ux uy dx dy : ℝ} (hb : 0 < b0) (hU : ux ^ 2 + uy ^ 2 = b0 ^ 2)
    (hD : dx ^ 2 + dy ^ 2 = b0 ^ 2) (hnd : ux * dy - uy * dx ≠ 0) :
    ∃ A B C Q : Mov, Tan b0 0 1 A B ∧ Tan b0 0 1 B C ∧ Tan b0 0 1 A Q ∧ Tan b0 0 1 Q C ∧
      Q.pos 0 = A.pos 0 + (C.pos 0 - B.pos 0) ∧
      (C.pos 0 - B.pos 0).re * (B.pos 0 - A.pos 0).im -
        (C.pos 0 - B.pos 0).im * (B.pos 0 - A.pos 0).re ≠ 0 ∧
      C.pos 0 - B.pos 0 = ⟨ux, uy⟩ ∧ B.pos 0 - A.pos 0 = ⟨dx, dy⟩ := by
  have hb' : b0 ≠ 0 := hb.ne'
  set A := still 0 (-dy / 2)
  set B := still dx (dy / 2)
  have hL := sideLen_contDiffAt b0 uy (dy / 2)
  have hcx : ContDiffAt ℝ 1 (fun c => dx + sideLen b0 uy (dy / 2) c * (ux / b0)) 0 :=
    contDiffAt_const.add (hL.mul contDiffAt_const)
  have hcy : ContDiffAt ℝ 1 (fun c => dy / 2 + sideLen b0 uy (dy / 2) c * (uy / b0)) 0 :=
    contDiffAt_const.add (hL.mul contDiffAt_const)
  set C := ofContDiff _ _ hcx hcy
  have hL0 : sideLen b0 uy (dy / 2) 0 = b0 := by simp [sideLen]
  have hAB : Tan b0 0 1 A B := by
    refine Eventually.of_forall fun c => ?_
    simp only [A, B, still]
    linear_combination hD
  have hBC : Tan b0 0 1 B C := by
    have hden : ∀ᶠ c in 𝓝 (0 : ℝ), 1 - c * (uy / (2 * b0)) ≠ 0 := by
      have hc : ContinuousAt (fun c : ℝ => 1 - c * (uy / (2 * b0))) 0 := by fun_prop
      exact hc.eventually_ne (by simp)
    filter_upwards [hden] with c hc
    simp only [B, C, still, ofContDiff]
    have hLdef : sideLen b0 uy (dy / 2) c * (1 - c * (uy / (2 * b0))) = b0 + c * (dy / 2) :=
      div_mul_cancel₀ _ hc
    generalize sideLen b0 uy (dy / 2) c = L at hLdef ⊢
    have key : b0 + c * (0 * (dx + (dx + L * (ux / b0))) +
        1 * (dy / 2 + (dy / 2 + L * (uy / b0)))) / 2 = L := by
      linear_combination -hLdef
    rw [key, show (dx + L * (ux / b0) - dx) ^ 2 + (dy / 2 + L * (uy / b0) - dy / 2) ^ 2 =
      L ^ 2 * (ux ^ 2 + uy ^ 2) / b0 ^ 2 by ring, hU]
    field_simp
  have hC0x : C.x 0 = dx + ux := by simp [C, ofContDiff, hL0]; field_simp
  have hC0y : C.y 0 = dy / 2 + uy := by simp [C, ofContDiff, hL0]; field_simp
  obtain ⟨Q, hqx, hqy, hAQ, hQC⟩ := apex_mov (b0 := b0) (hs := 0) (hc := 1) A C
    (q0 := (ux, -dy / 2 + uy)) contDiffAt_const contDiffAt_const hcx hcy
    (by simp only [A, still]; linear_combination hU)
    (by rw [hC0x, hC0y]; linear_combination hD)
    (by
      rw [hC0x, hC0y]
      simp only [A, still]
      intro h
      apply hnd
      linear_combination -h)
  have hA0 : A.pos 0 = ⟨0, -dy / 2⟩ := rfl
  have hB0 : B.pos 0 = ⟨dx, dy / 2⟩ := rfl
  have hC0 : C.pos 0 = ⟨dx + ux, dy / 2 + uy⟩ := pos_eq hC0x hC0y
  have hQ0 : Q.pos 0 = ⟨ux, -dy / 2 + uy⟩ := pos_eq hqx hqy
  refine ⟨A, B, C, Q, hAB, hBC, hAQ, hQC, ?_, ?_, ?_, ?_⟩
  · rw [hQ0, hA0, hB0, hC0]
    apply Complex.ext <;> simp
  · rw [hA0, hB0, hC0]
    simp only [Complex.sub_re, Complex.sub_im]
    intro h
    apply hnd
    linear_combination h
  · rw [hB0, hC0]
    apply Complex.ext <;> simp
  · rw [hA0, hB0]
    apply Complex.ext <;> simp
    ring

end Phyllotaxis.Apex
