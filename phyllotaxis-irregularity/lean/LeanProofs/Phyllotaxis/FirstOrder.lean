import Mathlib

/-!
# First-order transition lemmas for disk stacking with shrinking disks

Lemmas 1 and 3 of `open-questions/sunflower-phyllotaxis` (STATUS.md, PROOF_prop2.md). Disks of
diameter
`d = b0 + c η` where `η` is the height (a linear functional of the centre). Every configuration is
a family
of disk centres indexed by the rate `c`, differentiable at `c = 0`, in which the stated pairs of
disks are
tangent for all `c` near `0`. The lemmas compute the derivative at `c = 0`; with smoothness of the
family
(the apex is a transversal intersection of two circles, so the implicit function theorem applies)
this is
the statement `X = X₀ + c X'(0) + O(c²)` of the notes.

* `tangency_deriv`: differentiating one tangency gives `(Q - P)·(Q' - P') = b0 (η P + η Q)/2`.
* `rhombic_step` (Lemma 1): `ξ'(0) = i U D / b0` for the rhombic step on the notch
  `A -D-> B -U-> C`.
* `triangle_step` (Lemma 3): `ξ'(0) = i U² / (2 b0)` for the triangle on `B -U-> C`.
* `arg_deriv`: the angle `arg f(c)` of a family with `f 0 = 1` has derivative `Im f'(0)`.
* `cushion_rate`: the new hinge turns at rate `(1/2) cos(β_U - 60°)` (the cushion of Lemma 3).
* `split_rate`, `pass_rate`: the two first-order rotations behind the `N = 1` margin
  `(3/2) cos β_U |c|`.

Points are complex numbers `x + y i`; a moving point is a pair of real functions with derivatives
at `0`.
-/

namespace Phyllotaxis.FirstOrder

open Filter Topology Complex ComplexConjugate Real

/-- A disk centre depending on the rate `c`, differentiable at `c = 0`. -/
structure Mov where
  x : ℝ → ℝ
  y : ℝ → ℝ
  x' : ℝ
  y' : ℝ
  hx : HasDerivAt x x' 0
  hy : HasDerivAt y y' 0

namespace Mov

/-- Position at rate `c`, as a complex number. -/
def pos (P : Mov) (c : ℝ) : ℂ := ⟨P.x c, P.y c⟩

/-- Velocity `dP/dc` at `c = 0`. -/
def vel (P : Mov) : ℂ := ⟨P.x', P.y'⟩

theorem hasDerivAt_pos (P : Mov) : HasDerivAt P.pos P.vel 0 := by
  have h : P.pos = fun c => (P.x c : ℂ) + (P.y c : ℂ) * I := by
    funext c
    apply Complex.ext <;> simp [pos]
  have hd := (P.hx.ofReal_comp).add ((P.hy.ofReal_comp).mul_const I)
  rw [h]
  convert hd using 1
  apply Complex.ext <;> simp [vel]

end Mov

/-- Disks at `P` and `Q` are tangent for all small `c`, diameters `b0 + c (hs x + hc y)`. -/
def Tan (b0 hs hc : ℝ) (P Q : Mov) : Prop :=
  ∀ᶠ c in 𝓝 0, (Q.x c - P.x c) ^ 2 + (Q.y c - P.y c) ^ 2 =
    (b0 + c * (hs * (P.x c + Q.x c) + hc * (P.y c + Q.y c)) / 2) ^ 2

/-- At `c = 0` tangent disks are at distance `b0`. -/
theorem Tan.at_zero {b0 hs hc : ℝ} {P Q : Mov} (h : Tan b0 hs hc P Q) :
    (Q.x 0 - P.x 0) ^ 2 + (Q.y 0 - P.y 0) ^ 2 = b0 ^ 2 := by
  have := h.self_of_nhds
  simpa using this

/-- **Differentiated tangency.** -/
theorem tangency_deriv {b0 hs hc : ℝ} {P Q : Mov} (h : Tan b0 hs hc P Q) :
    (Q.x 0 - P.x 0) * (Q.x' - P.x') + (Q.y 0 - P.y 0) * (Q.y' - P.y') =
      b0 * (hs * (P.x 0 + Q.x 0) + hc * (P.y 0 + Q.y 0)) / 2 := by
  have hL := ((Q.hx.sub P.hx).pow 2).add ((Q.hy.sub P.hy).pow 2)
  have hR := ((((hasDerivAt_id (0 : ℝ)).mul
    (((P.hx.add Q.hx).const_mul hs).add ((P.hy.add Q.hy).const_mul hc))).div_const 2).const_add
      b0).pow 2
  have hR' := hR.congr_of_eventuallyEq h
  have := hL.unique hR'
  norm_num [Pi.add_apply, Pi.sub_apply, Pi.mul_apply] at this
  linarith

/-! ## Lemma 1: the rhombic step -/

/-- The linear system of Lemma 1: `U·ξ = -b0 D_y`, `D·ξ = -b0 U_y`, `|U| = |D| = b0`. -/
theorem rhombic_solve {ux uy dx dy b0 ξx ξy : ℝ} (hb : b0 ≠ 0) (hnd : ux * dy - uy * dx ≠ 0)
    (nU : ux ^ 2 + uy ^ 2 = b0 ^ 2) (nD : dx ^ 2 + dy ^ 2 = b0 ^ 2)
    (hU : ux * ξx + uy * ξy = -b0 * dy) (hD : dx * ξx + dy * ξy = -b0 * uy) :
    ξx = -(ux * dy + uy * dx) / b0 ∧ ξy = (ux * dx - uy * dy) / b0 := by
  constructor
  · rw [eq_div_iff hb]
    apply mul_left_cancel₀ hnd
    linear_combination b0 * dy * hU - b0 * uy * hD + dy ^ 2 * nU - uy ^ 2 * nD
  · rw [eq_div_iff hb]
    apply mul_left_cancel₀ hnd
    linear_combination b0 * ux * hD - b0 * dx * hU - dx * dy * nU + ux * uy * nD

theorem complex_of_parts {ξ u d : ℂ} {b0 : ℝ}
    (hre : ξ.re = -(u.re * d.im + u.im * d.re) / b0)
    (him : ξ.im = (u.re * d.re - u.im * d.im) / b0) :
    ξ = I * u * d / b0 := by
  apply Complex.ext
  · rw [hre, Complex.div_ofReal_re]
    simp
    ring
  · rw [him, Complex.div_ofReal_im]
    simp
    ring

/-- **Lemma 1 (rhombic step).** Notch `A -D-> B -U-> C` (`D = B - A`, `U = C - B`), new disk `Q`
tangent
to `A` and `C`, all four tangencies kept as `c` varies, heights `η = y`. At `c = 0` the new cell is
the
rhombus (`Q = A + U`). Then `ξ = (Q - A) - (C - B)` has `ξ'(0) = i U D / b0`, i.e.
`Q - A = U (1 + i c e^{i β_D}) + O(c²)`. -/
theorem rhombic_step {b0 : ℝ} (hb : 0 < b0) (A B C Q : Mov)
    (hAB : Tan b0 0 1 A B) (hBC : Tan b0 0 1 B C) (hAQ : Tan b0 0 1 A Q) (hQC : Tan b0 0 1 Q C)
    (hQ0 : Q.pos 0 = A.pos 0 + (C.pos 0 - B.pos 0))
    (hnd : (C.pos 0 - B.pos 0).re * (B.pos 0 - A.pos 0).im -
      (C.pos 0 - B.pos 0).im * (B.pos 0 - A.pos 0).re ≠ 0) :
    (Q.vel - A.vel) - (C.vel - B.vel) = I * (C.pos 0 - B.pos 0) * (B.pos 0 - A.pos 0) / b0 := by
  have e1 := tangency_deriv hAQ
  have e2 := tangency_deriv hBC
  have e3 := tangency_deriv hQC
  have e4 := tangency_deriv hAB
  have nU := hBC.at_zero
  have nD := hAB.at_zero
  have hx : Q.x 0 = A.x 0 + (C.x 0 - B.x 0) := by
    simpa [Mov.pos] using congrArg Complex.re hQ0
  have hy : Q.y 0 = A.y 0 + (C.y 0 - B.y 0) := by
    simpa [Mov.pos] using congrArg Complex.im hQ0
  simp only [Mov.pos, Complex.sub_re, Complex.sub_im] at hnd
  rw [hx, hy] at e1 e3
  obtain ⟨h1, h2⟩ := rhombic_solve (ξx := (Q.x' - A.x') - (C.x' - B.x'))
    (ξy := (Q.y' - A.y') - (C.y' - B.y')) hb.ne' hnd nU nD
    (by linear_combination e1 - e2) (by linear_combination e4 - e3)
  apply complex_of_parts
  · simpa [Mov.vel, Mov.pos] using h1
  · simpa [Mov.vel, Mov.pos] using h2

/-! ## Lemma 3: the triangle step -/

/-- `ω = e^{iπ/3}`. -/
noncomputable def ω : ℂ := ⟨1 / 2, √3 / 2⟩

theorem ω_ne : ω ≠ 0 := by
  intro h
  have := congrArg Complex.re h
  simp [ω] at this

/-- The linear system of Lemma 3: `(ωU)·ξ = b0 (√3 U_x - U_y)/4`, `(ω̄U)·ξ = -b0 (√3 U_x + U_y)/4`.
-/
theorem triangle_solve {ux uy b0 ξx ξy s3 : ℝ} (hb : 0 < b0) (hs3 : 0 < s3)
    (nU : ux ^ 2 + uy ^ 2 = b0 ^ 2)
    (hA : (ux / 2 - s3 * uy / 2) * ξx + (s3 * ux / 2 + uy / 2) * ξy = b0 * (s3 * ux - uy) / 4)
    (hB : (ux / 2 + s3 * uy / 2) * ξx + (-(s3 * ux / 2) + uy / 2) * ξy =
      -(b0 * (s3 * ux + uy) / 4)) :
    ξx = -(ux * uy) / b0 ∧ ξy = (ux ^ 2 - uy ^ 2) / 2 / b0 := by
  have hdet : -(s3 * ux ^ 2) / 2 - s3 * uy ^ 2 / 2 ≠ 0 := by
    have : -(s3 * ux ^ 2) / 2 - s3 * uy ^ 2 / 2 = -(s3 * b0 ^ 2) / 2 := by
      linear_combination (-(s3 / 2)) * nU
    rw [this]
    have : 0 < s3 * b0 ^ 2 := by positivity
    linarith
  constructor
  · rw [eq_div_iff hb.ne']
    apply mul_left_cancel₀ hdet
    linear_combination b0 * (-(s3 * ux / 2) + uy / 2) * hA - b0 * (s3 * ux / 2 + uy / 2) * hB +
      (-(s3 * ux * uy) / 2) * nU
  · rw [div_div, eq_div_iff (by positivity)]
    apply mul_left_cancel₀ hdet
    linear_combination 2 * (b0 * (ux / 2 - s3 * uy / 2) * hB - b0 * (ux / 2 + s3 * uy / 2) * hA +
      (s3 * ux ^ 2 / 4 - s3 * uy ^ 2 / 4) * nU)

theorem complex_of_parts_sq {ξ u : ℂ} {b0 : ℝ}
    (hre : ξ.re = -(u.re * u.im) / b0) (him : ξ.im = (u.re ^ 2 - u.im ^ 2) / 2 / b0) :
    ξ = I * u ^ 2 / (2 * b0) := by
  rw [show (2 * (b0 : ℂ)) = ((2 * b0 : ℝ) : ℂ) by push_cast; ring]
  apply Complex.ext
  · rw [hre, Complex.div_ofReal_re]
    simp [pow_two]
    ring
  · rw [him, Complex.div_ofReal_im]
    simp [pow_two]
    ring

/-- **Lemma 3 (triangle step).** Triangle on `B -U-> C`: new disk `Q` tangent to `B` and `C`, the
three
tangencies kept as `c` varies, heights `η = y`. At `c = 0`, `Q = B + ω U`. Then
`ξ = (Q - B) - ω (C - B)` has `ξ'(0) = i U² / (2 b0)`, i.e. `ξ = (i c / 2) e^{i β_U} U + O(c²)`. -/
theorem triangle_step {b0 : ℝ} (hb : 0 < b0) (B C Q : Mov)
    (hBC : Tan b0 0 1 B C) (hBQ : Tan b0 0 1 B Q) (hQC : Tan b0 0 1 Q C)
    (hQ0 : Q.pos 0 = B.pos 0 + ω * (C.pos 0 - B.pos 0)) :
    (Q.vel - B.vel) - ω * (C.vel - B.vel) = I * (C.pos 0 - B.pos 0) ^ 2 / (2 * b0) := by
  have e1 := tangency_deriv hBQ
  have e2 := tangency_deriv hBC
  have e3 := tangency_deriv hQC
  have nU := hBC.at_zero
  have h3 : √3 * √3 = 3 := Real.mul_self_sqrt (by norm_num)
  have hx : Q.x 0 = B.x 0 + ((C.x 0 - B.x 0) / 2 - √3 / 2 * (C.y 0 - B.y 0)) := by
    have := congrArg Complex.re hQ0
    simp [Mov.pos, ω] at this
    linarith
  have hy : Q.y 0 = B.y 0 + (√3 / 2 * (C.x 0 - B.x 0) + (C.y 0 - B.y 0) / 2) := by
    have := congrArg Complex.im hQ0
    simp [Mov.pos, ω] at this
    linarith
  rw [hx, hy] at e1 e3
  obtain ⟨h1, h2⟩ := triangle_solve (s3 := √3)
    (ξx := (Q.x' - B.x') - ((C.x' - B.x') / 2 - √3 / 2 * (C.y' - B.y')))
    (ξy := (Q.y' - B.y') - (√3 / 2 * (C.x' - B.x') + (C.y' - B.y') / 2))
    hb (by positivity) nU
    (by linear_combination e1 - e2 - ((C.x 0 - B.x 0) * (C.x' - B.x') +
      (C.y 0 - B.y 0) * (C.y' - B.y')) / 4 * h3)
    (by linear_combination e2 - e3 + ((C.x 0 - B.x 0) * (C.x' - B.x') +
      (C.y 0 - B.y 0) * (C.y' - B.y')) / 4 * h3)
  apply complex_of_parts_sq
  · simp only [Mov.vel, Mov.pos, ω, Complex.sub_re, Complex.mul_re, Complex.sub_im]
    rw [← h1]
    ring
  · simp only [Mov.vel, Mov.pos, ω, Complex.sub_re, Complex.mul_im, Complex.sub_im]
    rw [← h2]
    ring

/-! ## Angles: first-order rotation rates -/

/-- If `f 0 = 1`, the angle `arg f(c)` has derivative `Im f'(0)` at `0`. -/
theorem arg_deriv {f : ℝ → ℂ} {f' : ℂ} (hf : HasDerivAt f f' 0) (h1 : f 0 = 1) :
    HasDerivAt (fun c => arg (f c)) f'.im 0 := by
  have hlog := hf.clog_real (by rw [h1]; exact one_mem_slitPlane)
  rw [h1, div_one] at hlog
  have := Complex.imCLM.hasFDerivAt.comp_hasDerivAt (0 : ℝ) hlog
  simpa [Function.comp_def, Complex.log_im] using this

/-- If `F 0 = G 0 ≠ 0`, the relative angle `arg (F c / G c)` has derivative `Im ((F' - G') / G 0)`.
-/
theorem ratio_arg_deriv {F G : ℝ → ℂ} {F' G' : ℂ} (hF : HasDerivAt F F' 0) (hG : HasDerivAt G G' 0)
    (h0 : F 0 = G 0) (hne : G 0 ≠ 0) :
    HasDerivAt (fun c => arg (F c / G c)) ((F' - G') / G 0).im 0 := by
  have hq := hF.div hG hne
  have e : (F' * G 0 - F 0 * G') / G 0 ^ 2 = (F' - G') / G 0 := by
    rw [h0]
    field_simp
  rw [e] at hq
  exact arg_deriv hq (by simp [h0, hne])

theorem ω_eq : ω = exp (↑(π / 3) * I) := by
  apply Complex.ext
  · rw [Complex.exp_ofReal_mul_I_re, Real.cos_pi_div_three]
    simp [ω]
  · rw [Complex.exp_ofReal_mul_I_im, Real.sin_pi_div_three]
    simp [ω]

theorem ω_conj_add : conj ω + ω = 1 := by
  apply Complex.ext <;> simp [ω]
  ring

theorem ω_conj_mul : conj ω * ω = 1 := by
  have h3 : √3 * √3 = 3 := Real.mul_self_sqrt (by norm_num)
  apply Complex.ext <;> simp [ω] <;> nlinarith [h3]

theorem im_half_I_exp (θ : ℝ) : (I * exp (θ * I) / 2).im = Real.cos θ / 2 := by
  simp [Complex.div_ofNat_im, Complex.mul_im, Complex.exp_ofReal_mul_I_re]

/-- `(I U² / (2 b0)) / (ω U) = (I/2) e^{i(β - π/3)}` for `U = b0 e^{iβ}`. -/
theorem cushion_value {b0 β : ℝ} (hb : b0 ≠ 0) :
    I * (b0 * exp (β * I)) ^ 2 / (2 * b0) / (ω * (b0 * exp (β * I))) =
      I * exp (↑(β - π / 3) * I) / 2 := by
  have hb' : (b0 : ℂ) ≠ 0 := by exact_mod_cast hb
  rw [ω_eq]
  push_cast
  rw [show (↑β - ↑π / 3) * I = ↑β * I - ↑π / 3 * I by ring, Complex.exp_sub]
  field_simp

/-- **Cushion rate (Lemma 3).** In the triangle step, with `U = b0 e^{iβ}`, the new vector
`X = Q - B`
turns relative to `ω U` at rate `(1/2) cos(β - 60°)`; the new hinge at `B` is therefore
`60° + δ + (|c|/2) cos(β_U - 60°) + O(c²)` when the triangle fires at hinge `120° + δ`. -/
theorem cushion_rate {b0 β : ℝ} (hb : 0 < b0) (B C Q : Mov)
    (hBC : Tan b0 0 1 B C) (hBQ : Tan b0 0 1 B Q) (hQC : Tan b0 0 1 Q C)
    (hQ0 : Q.pos 0 = B.pos 0 + ω * (C.pos 0 - B.pos 0))
    (hU : C.pos 0 - B.pos 0 = b0 * exp (β * I)) :
    HasDerivAt (fun c => arg ((Q.pos c - B.pos c) / (ω * (C.pos c - B.pos c))))
      (Real.cos (β - π / 3) / 2) 0 := by
  have hξ := triangle_step hb B C Q hBC hBQ hQC hQ0
  have hF := Q.hasDerivAt_pos.sub B.hasDerivAt_pos
  have hG := (C.hasDerivAt_pos.sub B.hasDerivAt_pos).const_mul ω
  have hne : ω * (C.pos 0 - B.pos 0) ≠ 0 := by
    rw [hU]
    exact mul_ne_zero ω_ne (mul_ne_zero (by exact_mod_cast hb.ne') (Complex.exp_ne_zero _))
  have h0 : (Q.pos - B.pos) 0 = ω * (C.pos - B.pos) 0 := by
    simp only [Pi.sub_apply]
    rw [hQ0]
    ring
  have h := ratio_arg_deriv hF hG h0 hne
  simp only [Pi.sub_apply] at h
  convert h using 1
  rw [hξ, hU, cushion_value hb.ne', im_half_I_exp]

theorem ω_sq : ω ^ 2 = ω - 1 := by
  have h3 : √3 * √3 = 3 := Real.mul_self_sqrt (by norm_num)
  apply Complex.ext <;> simp [ω, pow_two] <;> nlinarith [h3]

theorem im_I_exp (θ : ℝ) : (I * exp (θ * I)).im = Real.cos θ := by
  simp [Complex.mul_im, Complex.exp_ofReal_mul_I_re]

/-- **Split rate (`N = 1`, creation).** After the triangle on `U = b0 e^{iβ}`, the two children
`X = Q - B` (`Ub/+`) and `Y = C - Q` (`Ub/−`) satisfy `arg X - arg Y = 2π/3 + (c/2) cos β + O(c²)`:
the relative angle `arg ((X ω̄) / (Y ω))` has derivative `cos β / 2`. -/
theorem split_rate {b0 β : ℝ} (hb : 0 < b0) (B C Q : Mov)
    (hBC : Tan b0 0 1 B C) (hBQ : Tan b0 0 1 B Q) (hQC : Tan b0 0 1 Q C)
    (hQ0 : Q.pos 0 = B.pos 0 + ω * (C.pos 0 - B.pos 0))
    (hU : C.pos 0 - B.pos 0 = b0 * exp (β * I)) :
    HasDerivAt (fun c => arg ((Q.pos c - B.pos c) * conj ω / ((C.pos c - Q.pos c) * ω)))
      (Real.cos β / 2) 0 := by
  have hξ := triangle_step hb B C Q hBC hBQ hQC hQ0
  have hF := (Q.hasDerivAt_pos.sub B.hasDerivAt_pos).mul_const (conj ω)
  have hG := (C.hasDerivAt_pos.sub Q.hasDerivAt_pos).mul_const ω
  have hb' : (b0 : ℂ) ≠ 0 := by exact_mod_cast hb.ne'
  have hG0 : (C.pos 0 - Q.pos 0) * ω = C.pos 0 - B.pos 0 := by
    rw [hQ0]
    linear_combination -(C.pos 0 - B.pos 0) * ω_sq
  have hF0 : (Q.pos 0 - B.pos 0) * conj ω = C.pos 0 - B.pos 0 := by
    rw [hQ0]
    linear_combination (C.pos 0 - B.pos 0) * ω_conj_mul
  have hne : (C.pos 0 - Q.pos 0) * ω ≠ 0 := by
    rw [hG0, hU]
    exact mul_ne_zero hb' (Complex.exp_ne_zero _)
  have h0 : (fun c => (Q.pos - B.pos) c * conj ω) 0 = (fun c => (C.pos - Q.pos) c * ω) 0 := by
    simp only [Pi.sub_apply]
    rw [hF0, hG0]
  have h := ratio_arg_deriv hF hG h0 hne
  simp only [Pi.sub_apply] at h
  convert h using 1
  have hnum : (Q.vel - B.vel) * conj ω - (C.vel - Q.vel) * ω =
      (Q.vel - B.vel) - ω * (C.vel - B.vel) := by
    linear_combination (Q.vel - B.vel) * ω_conj_add
  rw [hnum, hξ, hG0, hU,
    show I * (↑b0 * exp (↑β * I)) ^ 2 / (2 * ↑b0) / (↑b0 * exp (↑β * I)) = I * exp (↑β * I) / 2 by
      field_simp, im_half_I_exp]

/-- **Pass rate (`N = 1`, Lemma 1).** In a rhombic step with `U = b0 e^{iβ_U}`, the new down
`Y = C - Q` turns relative to the old down `D = B - A` at rate `-cos β_U`. -/
theorem pass_rate {b0 β : ℝ} (hb : 0 < b0) (A B C Q : Mov)
    (hAB : Tan b0 0 1 A B) (hBC : Tan b0 0 1 B C) (hAQ : Tan b0 0 1 A Q) (hQC : Tan b0 0 1 Q C)
    (hQ0 : Q.pos 0 = A.pos 0 + (C.pos 0 - B.pos 0))
    (hnd : (C.pos 0 - B.pos 0).re * (B.pos 0 - A.pos 0).im -
      (C.pos 0 - B.pos 0).im * (B.pos 0 - A.pos 0).re ≠ 0)
    (hU : C.pos 0 - B.pos 0 = b0 * exp (β * I)) :
    HasDerivAt (fun c => arg ((C.pos c - Q.pos c) / (B.pos c - A.pos c))) (-Real.cos β) 0 := by
  have hξ := rhombic_step hb A B C Q hAB hBC hAQ hQC hQ0 hnd
  have hF := C.hasDerivAt_pos.sub Q.hasDerivAt_pos
  have hG := B.hasDerivAt_pos.sub A.hasDerivAt_pos
  have hD : B.pos 0 - A.pos 0 ≠ 0 := by
    intro h
    rw [h] at hnd
    simp at hnd
  have h0 : (C.pos - Q.pos) 0 = (B.pos - A.pos) 0 := by
    simp only [Pi.sub_apply]
    rw [hQ0]
    ring
  have h := ratio_arg_deriv hF hG h0 hD
  simp only [Pi.sub_apply] at h
  convert h using 1
  have hb' : (b0 : ℂ) ≠ 0 := by exact_mod_cast hb.ne'
  rw [show C.vel - Q.vel - (B.vel - A.vel) = -((Q.vel - A.vel) - (C.vel - B.vel)) by ring, hξ, hU,
    show -(I * (↑b0 * exp (↑β * I)) * (B.pos 0 - A.pos 0) / ↑b0) / (B.pos 0 - A.pos 0) =
      -(I * exp (↑β * I)) by field_simp, Complex.neg_im, im_I_exp]

/-- **Up rotation per pass (Lemma 1).** In a rhombic step with `D = b0 e^{iβ_D}`, the new up
`X = Q - A`
turns relative to the old up `U = C - B` at rate `cos β_D`: `U' = U (1 + i c e^{iβ_D}) + O(c²)`. -/
theorem up_pass_rate {b0 β : ℝ} (hb : 0 < b0) (A B C Q : Mov)
    (hAB : Tan b0 0 1 A B) (hBC : Tan b0 0 1 B C) (hAQ : Tan b0 0 1 A Q) (hQC : Tan b0 0 1 Q C)
    (hQ0 : Q.pos 0 = A.pos 0 + (C.pos 0 - B.pos 0))
    (hnd : (C.pos 0 - B.pos 0).re * (B.pos 0 - A.pos 0).im -
      (C.pos 0 - B.pos 0).im * (B.pos 0 - A.pos 0).re ≠ 0)
    (hD : B.pos 0 - A.pos 0 = b0 * exp (β * I)) :
    HasDerivAt (fun c => arg ((Q.pos c - A.pos c) / (C.pos c - B.pos c))) (Real.cos β) 0 := by
  have hξ := rhombic_step hb A B C Q hAB hBC hAQ hQC hQ0 hnd
  have hF := Q.hasDerivAt_pos.sub A.hasDerivAt_pos
  have hG := C.hasDerivAt_pos.sub B.hasDerivAt_pos
  have hU : C.pos 0 - B.pos 0 ≠ 0 := by
    intro h
    rw [h] at hnd
    simp at hnd
  have h0 : (Q.pos - A.pos) 0 = (C.pos - B.pos) 0 := by
    simp only [Pi.sub_apply]
    rw [hQ0]
    ring
  have h := ratio_arg_deriv hF hG h0 hU
  simp only [Pi.sub_apply] at h
  convert h using 1
  have hb' : (b0 : ℂ) ≠ 0 := by exact_mod_cast hb.ne'
  rw [hξ, hD, show I * (C.pos 0 - B.pos 0) * (↑b0 * exp (↑β * I)) / ↑b0 / (C.pos 0 - B.pos 0) =
      I * exp (↑β * I) by field_simp, im_I_exp]

/-- The hinge sum of the `DDU` triple `(Ub/−, D, Ub/+)` minus `240°` depends only on the two
children:
`h(v, w) = arg v + π - arg w`, and `D` drops out. -/
theorem ddu_hinge_sum (aYm aD aYp : ℝ) :
    (aYm + π - aD) + (aD + π - aYp) - 4 * π / 3 = 2 * π / 3 - (aYp - aYm) := by
  ring

/-- `cos(β - 60°) + cos(β + 60°) = cos β`: the two halves of the split rate. -/
theorem cos_split (β : ℝ) : Real.cos (β - π / 3) + Real.cos (β + π / 3) = Real.cos β := by
  rw [Real.cos_sub, Real.cos_add, Real.cos_pi_div_three]
  ring

/-- **`N = 1` margin.** Creation contributes `(c/2) cos β` to `arg Ub/+ - arg Ub/−` (`split_rate`),
the pass
that forms the `DDU` triple turns `Ub/−` by `-c cos β` (`pass_rate`); the `DDU` margin
`2π/3 - (arg Ub/+ - arg Ub/−)` is then `(3/2) |c| cos β` for `c ≤ 0`, at first order. -/
theorem n1_margin {c β : ℝ} (hc : c ≤ 0) :
    2 * π / 3 - (2 * π / 3 + c * (Real.cos β / 2) - c * (-Real.cos β)) =
      3 / 2 * |c| * Real.cos β := by
  rw [abs_of_nonpos hc]
  ring

end Phyllotaxis.FirstOrder
