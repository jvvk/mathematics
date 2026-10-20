import LeanProofs.Phyllotaxis.Static
import LeanProofs.Phyllotaxis.Apex

/-!
# Theorem C is not vacuous

For all rates `α, σ, ε, k` and every height direction `(Wr, Wi)`, there is a `Front`
(`Static.lean`): five disks built one after another with closed-form side lengths (each new disk
touches the previous one with diameters `1 + t k H`), turning at the prescribed rates, and the four
apex families at `Q0` from the implicit function theorem (`Apex.apex_mov`). So every hypothesis of
`Static.pentagon_first` is satisfiable.
-/

namespace Phyllotaxis.StaticExists

open Filter Topology Complex Real
open Phyllotaxis.FirstOrder Phyllotaxis.Apex Phyllotaxis.Static

/-- A moving disk following a `C¹` complex path. -/
noncomputable def ofPath (p : ℝ → ℂ) (hp : ContDiffAt ℝ 1 p 0) : Mov where
  x := fun t => (p t).re
  y := fun t => (p t).im
  x' := (deriv p 0).re
  y' := (deriv p 0).im
  hx := by
    have := reCLM.hasFDerivAt.comp_hasDerivAt (0 : ℝ) ((hp.differentiableAt one_ne_zero).hasDerivAt)
    simpa [Function.comp_def] using this
  hy := by
    have := imCLM.hasFDerivAt.comp_hasDerivAt (0 : ℝ) ((hp.differentiableAt one_ne_zero).hasDerivAt)
    simpa [Function.comp_def] using this

theorem ofPath_pos (p : ℝ → ℂ) (hp : ContDiffAt ℝ 1 p 0) (t : ℝ) : (ofPath p hp).pos t = p t := by
  apply Complex.ext <;> rfl

theorem ofPath_cx {p : ℝ → ℂ} (hp : ContDiffAt ℝ 1 p 0) : ContDiffAt ℝ 1 (ofPath p hp).x 0 :=
  reCLM.contDiff.contDiffAt.comp 0 hp

theorem ofPath_cy {p : ℝ → ℂ} (hp : ContDiffAt ℝ 1 p 0) : ContDiffAt ℝ 1 (ofPath p hp).y 0 :=
  imCLM.contDiff.contDiffAt.comp 0 hp

/-- Tangency is symmetric. -/
theorem Tan.symm {b0 hs hc : ℝ} {P Q : Mov} (h : Tan b0 hs hc P Q) : Tan b0 hs hc Q P := by
  filter_upwards [h] with t ht
  linear_combination ht

section Step

variable (k Wr Wi : ℝ)

/-- Height `H z = Wi x + Wr y`. -/
def hgt (z : ℂ) : ℝ := Wi * z.re + Wr * z.im

/-- Side length from a disk at height `h` in direction `θ`: `L (1 - t k H(e^{iθ})/2) = 1 + t k h`.
-/
noncomputable def len (s : ℝ → ℂ) (θ : ℝ → ℝ) (t : ℝ) : ℝ :=
  (1 + t * k * hgt Wr Wi (s t)) / (1 - t * k * (Wi * Real.cos (θ t) + Wr * Real.sin (θ t)) / 2)

/-- The next disk: `s + L e^{iθ}`. -/
noncomputable def next (s : ℝ → ℂ) (θ : ℝ → ℝ) (t : ℝ) : ℂ :=
  s t + (len k Wr Wi s θ t : ℂ) * exp (θ t * I)

variable {k Wr Wi}

theorem den_ne {θ : ℝ → ℝ} (hθ : ContinuousAt θ 0) :
    ∀ᶠ t in 𝓝 (0 : ℝ), 1 - t * k * (Wi * Real.cos (θ t) + Wr * Real.sin (θ t)) / 2 ≠ 0 := by
  have hc : ContinuousAt (fun t => 1 - t * k * (Wi * Real.cos (θ t) + Wr * Real.sin (θ t)) / 2) 0 :=
    by fun_prop
  exact hc.eventually_ne (by simp)

theorem len_contDiffAt {s : ℝ → ℂ} {θ : ℝ → ℝ} (hs : ContDiffAt ℝ 1 s 0) (hθ : ContDiffAt ℝ 1 θ 0) :
    ContDiffAt ℝ 1 (len k Wr Wi s θ) 0 := by
  unfold len hgt
  apply ContDiffAt.div
  · exact contDiffAt_const.add ((contDiffAt_id.mul contDiffAt_const).mul
      ((contDiffAt_const.mul (reCLM.contDiff.contDiffAt.comp 0 hs)).add
        (contDiffAt_const.mul (imCLM.contDiff.contDiffAt.comp 0 hs))))
  · exact contDiffAt_const.sub (((contDiffAt_id.mul contDiffAt_const).mul
      ((contDiffAt_const.mul (Real.contDiff_cos.contDiffAt.comp 0 hθ)).add
        (contDiffAt_const.mul (Real.contDiff_sin.contDiffAt.comp 0 hθ)))).div_const 2)
  · simp

theorem next_contDiffAt {s : ℝ → ℂ} {θ : ℝ → ℝ} (hs : ContDiffAt ℝ 1 s 0) (hθ : ContDiffAt ℝ 1 θ 0)
:     ContDiffAt ℝ 1 (next k Wr Wi s θ) 0 := by
  unfold next
  apply hs.add
  apply ContDiffAt.mul
  · exact ofRealCLM.contDiff.contDiffAt.comp 0 (len_contDiffAt hs hθ)
  · exact Complex.contDiff_exp.contDiffAt.comp 0
      ((ofRealCLM.contDiff.contDiffAt.comp 0 hθ).mul contDiffAt_const)

theorem len_zero (s : ℝ → ℂ) (θ : ℝ → ℝ) : len k Wr Wi s θ 0 = 1 := by simp [len]

/-- **The step keeps tangency.** The next disk touches the previous one for all small `t`. -/
theorem tan_next {s : ℝ → ℂ} {θ : ℝ → ℝ} (hs : ContDiffAt ℝ 1 s 0) (hθ : ContDiffAt ℝ 1 θ 0) :
    Tan 1 (k * Wi) (k * Wr) (ofPath s hs) (ofPath (next k Wr Wi s θ) (next_contDiffAt hs hθ)) := by
  filter_upwards [den_ne (k := k) (Wr := Wr) (Wi := Wi) hθ.continuousAt] with t hd
  simp only [ofPath, next, Complex.add_re, Complex.add_im, Complex.re_ofReal_mul,
    Complex.im_ofReal_mul, Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im]
  have hL : len k Wr Wi s θ t * (1 - t * k * (Wi * Real.cos (θ t) + Wr * Real.sin (θ t)) / 2) =
      1 + t * k * hgt Wr Wi (s t) := by
    unfold len
    exact div_mul_cancel₀ _ hd
  have hcs := Real.cos_sq_add_sin_sq (θ t)
  unfold hgt at hL
  linear_combination (len k Wr Wi s θ t) ^ 2 * hcs + ((len k Wr Wi s θ t) +
    (1 + t * (k * Wi * ((s t).re + ((s t).re + len k Wr Wi s θ t * Real.cos (θ t))) +
      k * Wr * ((s t).im + ((s t).im + len k Wr Wi s θ t * Real.sin (θ t)))) / 2)) * hL

end Step

/-- `arg ((r₁ e^{ia}) / (r₂ e^{ib})) = a - b` for positive `r₁, r₂` and `a - b ∈ (-π, π]`. -/
theorem arg_quot {r1 r2 a b : ℝ} (h1 : 0 < r1) (h2 : 0 < r2) (hab : a - b ∈ Set.Ioc (-π) π) :
    arg (((r1 : ℂ) * exp (a * I)) / ((r2 : ℂ) * exp (b * I))) = a - b := by
  have e : ((r1 : ℂ) * exp (a * I)) / ((r2 : ℂ) * exp (b * I)) =
      ((r1 / r2 : ℝ) : ℂ) * (Complex.cos ((a - b : ℝ)) + Complex.sin ((a - b : ℝ)) * I) := by
    rw [← Complex.exp_mul_I, mul_div_mul_comm, ← Complex.exp_sub]
    push_cast
    ring_nf
  rw [e, arg_mul_cos_add_sin_mul_I (div_pos h1 h2) hab]

/-- A `C¹` function equal to `1` at `0` is eventually positive. -/
theorem eventually_pos_one {f : ℝ → ℝ} (hf : ContinuousAt f 0) (h0 : f 0 = 1) :
    ∀ᶠ t in 𝓝 (0 : ℝ), 0 < f t := by
  have := hf.eventually (lt_mem_nhds (show (0 : ℝ) < f 0 by rw [h0]; norm_num))
  exact this

/-- `r t ∈ (-π, π]` for small `t` when `r` is linear. -/
theorem eventually_Ioc (r : ℝ) : ∀ᶠ t in 𝓝 (0 : ℝ), r * t ∈ Set.Ioc (-π) π := by
  have hc : ContinuousAt (fun t : ℝ => r * t) 0 := by fun_prop
  have := hc.eventually (Ioo_mem_nhds (show -π < r * 0 by simp [Real.pi_pos])
    (show r * 0 < π by simp [Real.pi_pos]))
  filter_upwards [this] with t ht
  exact ⟨ht.1, ht.2.le⟩

/-- **Non-vacuity of Theorem C.** For all rates and height directions there are a perturbed front
and the four apex families at `Q0`, satisfying every hypothesis of `Static.pentagon_first` other
than the window. -/
theorem front_exists (α σ ε k Wr Wi : ℝ) :
    ∃ F : Front α σ ε k Wr Wi, ∃ Q Qr Qt Qw : Mov,
      (Q.x 0 = 3 / 2 ∧ Q.y 0 = √3 / 2) ∧ (Qr.x 0 = 3 / 2 ∧ Qr.y 0 = √3 / 2) ∧
      (Qt.x 0 = 3 / 2 ∧ Qt.y 0 = √3 / 2) ∧ (Qw.x 0 = 3 / 2 ∧ Qw.y 0 = √3 / 2) ∧
      Tan 1 (k * Wi) (k * Wr) F.A Q ∧ Tan 1 (k * Wi) (k * Wr) Q F.E ∧
      Tan 1 (k * Wi) (k * Wr) F.A Qr ∧ Tan 1 (k * Wi) (k * Wr) Qr F.C ∧
      Tan 1 (k * Wi) (k * Wr) F.C Qt ∧ Tan 1 (k * Wi) (k * Wr) Qt F.E ∧
      Tan 1 (k * Wi) (k * Wr) F.Z Qw ∧ Tan 1 (k * Wi) (k * Wr) Qw F.C := by
  have h3 : √3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  -- the five paths
  set b : ℝ → ℂ := fun _ => 0
  have hb : ContDiffAt ℝ 1 b 0 := contDiffAt_const
  set θC : ℝ → ℝ := fun _ => 0
  set θE : ℝ → ℝ := fun t => ε * t
  set θA : ℝ → ℝ := fun t => π / 3 + σ * t
  set θZ : ℝ → ℝ := fun t => π / 3 + (σ + α) * t
  have hθC : ContDiffAt ℝ 1 θC 0 := contDiffAt_const
  have hθE : ContDiffAt ℝ 1 θE 0 := contDiffAt_const.mul contDiffAt_id
  have hθA : ContDiffAt ℝ 1 θA 0 := contDiffAt_const.add (contDiffAt_const.mul contDiffAt_id)
  have hθZ : ContDiffAt ℝ 1 θZ 0 := contDiffAt_const.add (contDiffAt_const.mul contDiffAt_id)
  set c := next k Wr Wi b θC
  have hc := next_contDiffAt (k := k) (Wr := Wr) (Wi := Wi) hb hθC
  set e := next k Wr Wi c θE
  have he := next_contDiffAt (k := k) (Wr := Wr) (Wi := Wi) hc hθE
  set a := next k Wr Wi b θA
  have ha := next_contDiffAt (k := k) (Wr := Wr) (Wi := Wi) hb hθA
  set z := next k Wr Wi a θZ
  have hz := next_contDiffAt (k := k) (Wr := Wr) (Wi := Wi) ha hθZ
  set B := ofPath b hb
  set C := ofPath c hc
  set E := ofPath e he
  set A := ofPath a ha
  set Z := ofPath z hz
  -- positions at 0
  have p3c : Real.cos (π / 3) = 1 / 2 := Real.cos_pi_div_three
  have p3s : Real.sin (π / 3) = √3 / 2 := Real.sin_pi_div_three
  have nx : ∀ (s : ℝ → ℂ) (θ : ℝ → ℝ), (next k Wr Wi s θ 0).re = (s 0).re + Real.cos (θ 0) := by
    intro s θ
    simp [next, len_zero, Complex.exp_ofReal_mul_I_re]
  have ny : ∀ (s : ℝ → ℂ) (θ : ℝ → ℝ), (next k Wr Wi s θ 0).im = (s 0).im + Real.sin (θ 0) := by
    intro s θ
    simp [next, len_zero, Complex.exp_ofReal_mul_I_im]
  have hB0 : B.x 0 = 0 ∧ B.y 0 = 0 := by simp [B, b, ofPath]
  have hC0 : C.x 0 = 1 ∧ C.y 0 = 0 := by
    refine ⟨?_, ?_⟩ <;> simp only [C, ofPath] <;> [rw [nx]; rw [ny]] <;> simp [b, θC]
  have hE0 : E.x 0 = 2 ∧ E.y 0 = 0 := by
    refine ⟨?_, ?_⟩ <;> simp only [E, ofPath] <;> [rw [nx, nx]; rw [ny, ny]] <;>
      simp [b, θC, θE]; norm_num
  have hA0 : A.x 0 = 1 / 2 ∧ A.y 0 = √3 / 2 := by
    refine ⟨?_, ?_⟩ <;> simp only [A, ofPath] <;> [rw [nx]; rw [ny]] <;> simp [b, θA, p3c, p3s]
  have hZ0 : Z.x 0 = 1 ∧ Z.y 0 = √3 := by
    refine ⟨?_, ?_⟩ <;> simp only [Z, ofPath] <;> [rw [nx, nx]; rw [ny, ny]] <;>
      simp [b, θA, θZ, p3c, p3s]; ring
  -- tangencies of the front
  have tBC : Tan 1 (k * Wi) (k * Wr) B C := tan_next hb hθC
  have tCE : Tan 1 (k * Wi) (k * Wr) C E := tan_next hc hθE
  have tAB : Tan 1 (k * Wi) (k * Wr) A B := Tan.symm (tan_next hb hθA)
  have tZA : Tan 1 (k * Wi) (k * Wr) Z A := Tan.symm (tan_next ha hθZ)
  -- side lengths are eventually positive
  have lpos : ∀ (s : ℝ → ℂ) (θ : ℝ → ℝ), ContDiffAt ℝ 1 s 0 → ContDiffAt ℝ 1 θ 0 →
      ∀ᶠ t in 𝓝 (0 : ℝ), 0 < len k Wr Wi s θ t := fun s θ hs hθ =>
    eventually_pos_one (len_contDiffAt hs hθ).continuousAt (len_zero s θ)
  -- hinge rates
  have dpos : ∀ (s : ℝ → ℂ) (θ : ℝ → ℝ) (t : ℝ),
      next k Wr Wi s θ t - s t = (len k Wr Wi s θ t : ℂ) * exp (θ t * I) := by
    intro s θ t
    simp [next]
  have hα : HasDerivAt (fun t => arg ((A.pos t - Z.pos t) / (B.pos t - A.pos t))) α 0 := by
    have hlin : HasDerivAt (fun t : ℝ => α * t) α 0 := by
      simpa using (hasDerivAt_id (0 : ℝ)).const_mul α
    apply hlin.congr_of_eventuallyEq
    filter_upwards [lpos a θZ ha hθZ, lpos b θA hb hθA, eventually_Ioc α] with t h1 h2 h3'
    simp only [ofPath_pos, A, Z, B]
    have e1 : a t - z t = -((len k Wr Wi a θZ t : ℂ) * exp (θZ t * I)) := by
      rw [← dpos a θZ t]; ring
    have e2 : b t - a t = -((len k Wr Wi b θA t : ℂ) * exp (θA t * I)) := by
      rw [← dpos b θA t]; ring
    rw [e1, e2, neg_div_neg_eq, arg_quot h1 h2]
    · simp only [θZ, θA]; ring
    · have : θZ t - θA t = α * t := by simp only [θZ, θA]; ring
      rw [this]; exact h3'
  have hσ : HasDerivAt (fun t => arg ((B.pos t - A.pos t) / (-ω * (C.pos t - B.pos t)))) σ 0 := by
    have hlin : HasDerivAt (fun t : ℝ => σ * t) σ 0 := by
      simpa using (hasDerivAt_id (0 : ℝ)).const_mul σ
    apply hlin.congr_of_eventuallyEq
    filter_upwards [lpos b θA hb hθA, lpos b θC hb hθC, eventually_Ioc σ] with t h1 h2 h3'
    simp only [ofPath_pos, A, C, B]
    have e2 : b t - a t = -((len k Wr Wi b θA t : ℂ) * exp (θA t * I)) := by
      rw [← dpos b θA t]; ring
    have e3 : -ω * (c t - b t) = -((len k Wr Wi b θC t : ℂ) * exp (↑(π / 3) * I)) := by
      rw [dpos b θC t, ω_eq]; simp [θC]; ring
    rw [e2, e3, neg_div_neg_eq, arg_quot h1 h2]
    · simp only [θA]; ring
    · have : θA t - π / 3 = σ * t := by simp only [θA]; ring
      rw [this]; exact h3'
  have hε : HasDerivAt (fun t => arg ((C.pos t - B.pos t) / (E.pos t - C.pos t))) (-ε) 0 := by
    have hlin : HasDerivAt (fun t : ℝ => -ε * t) (-ε) 0 := by
      simpa using (hasDerivAt_id (0 : ℝ)).const_mul (-ε)
    apply hlin.congr_of_eventuallyEq
    filter_upwards [lpos b θC hb hθC, lpos c θE hc hθE, eventually_Ioc (-ε)] with t h1 h2 h3'
    simp only [ofPath_pos, C, E, B]
    have e3 : c t - b t = (len k Wr Wi b θC t : ℂ) * exp (θC t * I) := dpos b θC t
    have e4 : e t - c t = (len k Wr Wi c θE t : ℂ) * exp (θE t * I) := dpos c θE t
    rw [e3, e4, arg_quot h1 h2]
    · simp only [θC, θE]; ring
    · have : θC t - θE t = -ε * t := by simp only [θC, θE]; ring
      rw [this]; exact h3'
  let F : Front α σ ε k Wr Wi :=
    ⟨Z, A, B, C, E, hZ0, hA0, hB0, hC0, hE0, tZA, tAB, tBC, tCE, hα, hσ, hε⟩
  -- the apex families
  have q2 : ∀ {px py : ℝ}, (3 / 2 - px) ^ 2 + (√3 / 2 - py) ^ 2 = 1 →
      (px - 3 / 2) ^ 2 + (py - √3 / 2) ^ 2 = 1 := fun h => by linear_combination h
  have dA : (3 / 2 - 1 / 2 : ℝ) ^ 2 + (√3 / 2 - √3 / 2) ^ 2 = 1 := by ring
  have dC : (3 / 2 - 1 : ℝ) ^ 2 + (√3 / 2 - 0) ^ 2 = 1 := by linear_combination (1 / 4) * h3
  have dE : (3 / 2 - 2 : ℝ) ^ 2 + (√3 / 2 - 0) ^ 2 = 1 := by linear_combination (1 / 4) * h3
  have dZ : (3 / 2 - 1 : ℝ) ^ 2 + (√3 / 2 - √3) ^ 2 = 1 := by linear_combination (1 / 4) * h3
  have s3 : (0 : ℝ) < √3 := by positivity
  obtain ⟨Q, hQx, hQy, tAQ, tQE⟩ := apex_mov (b0 := 1) (hs := k * Wi) (hc := k * Wr) A E
    (q0 := (3 / 2, √3 / 2)) (ofPath_cx ha) (ofPath_cy ha) (ofPath_cx he) (ofPath_cy he)
    (by rw [hA0.1, hA0.2]; simpa using dA) (by rw [hE0.1, hE0.2]; simpa using q2 dE)
    (by rw [hA0.1, hA0.2, hE0.1, hE0.2]; ring_nf; positivity)
  obtain ⟨Qr, hQrx, hQry, tAQr, tQrC⟩ := apex_mov (b0 := 1) (hs := k * Wi) (hc := k * Wr) A C
    (q0 := (3 / 2, √3 / 2)) (ofPath_cx ha) (ofPath_cy ha) (ofPath_cx hc) (ofPath_cy hc)
    (by rw [hA0.1, hA0.2]; simpa using dA) (by rw [hC0.1, hC0.2]; simpa using q2 dC)
    (by rw [hA0.1, hA0.2, hC0.1, hC0.2]; ring_nf; positivity)
  obtain ⟨Qt, hQtx, hQty, tCQt, tQtE⟩ := apex_mov (b0 := 1) (hs := k * Wi) (hc := k * Wr) C E
    (q0 := (3 / 2, √3 / 2)) (ofPath_cx hc) (ofPath_cy hc) (ofPath_cx he) (ofPath_cy he)
    (by rw [hC0.1, hC0.2]; simpa using dC) (by rw [hE0.1, hE0.2]; simpa using q2 dE)
    (by rw [hC0.1, hC0.2, hE0.1, hE0.2]; ring_nf; positivity)
  obtain ⟨Qw, hQwx, hQwy, tZQw, tQwC⟩ := apex_mov (b0 := 1) (hs := k * Wi) (hc := k * Wr) Z C
    (q0 := (3 / 2, √3 / 2)) (ofPath_cx hz) (ofPath_cy hz) (ofPath_cx hc) (ofPath_cy hc)
    (by rw [hZ0.1, hZ0.2]; simpa using dZ) (by rw [hC0.1, hC0.2]; simpa using q2 dC)
    (by rw [hZ0.1, hZ0.2, hC0.1, hC0.2]; ring_nf; positivity)
  exact ⟨F, Q, Qr, Qt, Qw, ⟨hQx, hQy⟩, ⟨hQrx, hQry⟩, ⟨hQtx, hQty⟩, ⟨hQwx, hQwy⟩,
    tAQ, tQE, tAQr, tQrC, tCQt, tQtE, tZQw, tQwC⟩

end Phyllotaxis.StaticExists
