import LeanProofs.Phyllotaxis.FirstOrder

/-!
# Theorem C: the first disk on a near-lattice front with a 60° notch is a pentagon

`open-questions/sunflower-phyllotaxis/PROOF_static.md`. Near the rhombic lattice front with `m` down
vectors, `n` up vectors and notch hinge exactly `60°` (the notch-60 law `tan u = √3 m / (2n - m)`),
the lowest site `Q0` touches four front disks `Z, A, C, E` (`Z`, `E` diametrically opposite).
Perturb the hinges at `A`, `B`, `C` at rates `α`, `σ`, `-ε` and shrink the disks at rate `k`
(diameter `1 + t k H`, `H` the height). The first-order clearances of the six candidate positions at
`Q0` are exact linear forms; the pentagon (the disk touching `A` and `E`) is free and lowest exactly
on the window `(ε - α)/2 - |k| sin(u + 30°) < σ < ε - |k| (√3 sin u + 5 cos u)/4`.

Frame: rigid motions do not change clearances, so the zeroth-order disks are placed with `B = 0` and
the first up vector along `1`: `A = ω`, `B = 0`, `C = 1`, `E = 2`, `Z = 2ω`, `Q0 = 1 + ω`. The
height is `H z = Im (W z) = Wi x + Wr y` with `W = e^{iu}` the real-frame bearing of the up vectors.

* `notch60_tan`: the closing law of the notch-60 lattice.
* `lattice_Q0`: `Q0` is at distance `1` from `Z, A, C, E`, `√3` from `B`, and `|Z - E| = 2`; the
  apexes over the arm vectors.
* `clr_deriv`, `eventually_pos_of_deriv`: first-order clearances and their sign for small `t > 0`.
* `pentagon_clear_C`, `pentagon_clear_Z`: the pentagon's clearances have derivatives `2P`, `2R`.
* `rhombus_hits_E`, `triangle_hits_A`, `zc_hits_A`: the competitors at `Q0` overlap at rates `-2P`,
  `-2P`, `-2(P + R)`; `za_higher`: the disk touching `Z, A` is higher by `(2/√3) R cos u`;
  `channel_rate`: the gap between `Z` and `E` opens at rate `R`.
* `window_iff`: `P > 0 ∧ R > 0` is the window (for `k ≤ 0`).
* `pentagon_first`: on the window, for small `t > 0` the pentagon is clear of `C` and `Z` and the
  three competitors overlap a disk.
-/

namespace Phyllotaxis.Static

open Filter Topology Complex ComplexConjugate Real
open Phyllotaxis.FirstOrder

/-! ## The notch-60 law -/

theorem notch60_identity (m n u : ℝ) :
    2 * (m * Real.sin (u - 2 * π / 3) + n * Real.sin u) =
      (2 * n - m) * Real.sin u - √3 * m * Real.cos u := by
  have e : u - 2 * π / 3 = (u + π / 3) - π := by ring
  rw [e, Real.sin_sub_pi, Real.sin_add, Real.sin_pi_div_three, Real.cos_pi_div_three]
  ring

/-- **Notch-60 law.** `m` downs at bearing `u - 120°` and `n` ups at bearing `u` (notch hinge `60°`)
have zero total height iff `tan u = √3 m / (2n - m)`. For `(2,3)`: `tan u = √3/2`. -/
theorem notch60_tan {m n u : ℝ} (hu : Real.cos u ≠ 0) (h : 2 * n - m ≠ 0) :
    m * Real.sin (u - 2 * π / 3) + n * Real.sin u = 0 ↔ Real.tan u = √3 * m / (2 * n - m) := by
  have hI := notch60_identity m n u
  rw [Real.tan_eq_sin_div_cos, div_eq_div_iff hu h]
  constructor
  · intro h0
    rw [h0] at hI
    linarith
  · intro h1
    linarith

/-! ## The lattice at `Q0` (zeroth order, rotated frame) -/

/-- Squared distance in coordinates. -/
noncomputable def d2 (p q : ℝ × ℝ) : ℝ := (q.1 - p.1) ^ 2 + (q.2 - p.2) ^ 2

/-- `Q0 = 1 + ω` touches `Z = 2ω`, `A = ω`, `C = 1`, `E = 2`, is `√3` from `B = 0`, and is the
midpoint of `Z` and `E`, which are two diameters apart. The apex over the arm vector `Z → A` and
over `C → E` is `Q0`; over `A → B` it is `C` and over `B → C` it is `A` (occupied). -/
theorem lattice_Q0 :
    let Z : ℝ × ℝ := (1, √3); let A : ℝ × ℝ := (1 / 2, √3 / 2); let B : ℝ × ℝ := (0, 0)
    let C : ℝ × ℝ := (1, 0); let E : ℝ × ℝ := (2, 0); let Q : ℝ × ℝ := (3 / 2, √3 / 2)
    d2 Z Q = 1 ∧ d2 A Q = 1 ∧ d2 C Q = 1 ∧ d2 E Q = 1 ∧ d2 B Q = 3 ∧ d2 Z E = 4 ∧
      Q = ((Z.1 + E.1) / 2, (Z.2 + E.2) / 2) := by
  intro Z A B C E Q
  have h3 : √3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp only [d2, Z, A, B, C, E, Q, Prod.mk.injEq] <;>
    first | (constructor <;> ring) | linear_combination h3 | linear_combination (1 / 4) * h3 |
      linear_combination (3 / 4) * h3 | ring

/-- Apex over a front vector `p → p + v` (unit diameters): `p + v ω`. Over `Z → A` and `C → E` it is
`Q0`; over `A → B` it is `C`; over `B → C` it is `A`. -/
theorem arm_apexes :
    (2 * ω + (ω - 2 * ω) * ω = 1 + ω) ∧ ((1 : ℂ) + (2 - 1) * ω = 1 + ω) ∧
      (ω + (0 - ω) * ω = 1) ∧ ((0 : ℂ) + (1 - 0) * ω = ω) := by
  have hs := ω_sq
  exact ⟨by linear_combination (-1 : ℂ) * hs, by ring, by linear_combination (-1 : ℂ) * hs, by ring⟩

/-! ## Clearances and their first-order sign -/

/-- Squared-distance defect of disks `P`, `Q` with diameters `1 + t (hs x + hc y)`: positive when
they are apart, zero when they touch, negative when they overlap. -/
noncomputable def clr (hs hc : ℝ) (P Q : Mov) (t : ℝ) : ℝ :=
  (Q.x t - P.x t) ^ 2 + (Q.y t - P.y t) ^ 2 -
    (1 + t * (hs * (P.x t + Q.x t) + hc * (P.y t + Q.y t)) / 2) ^ 2

/-- First-order clearance of `Q` from `P` (the derivative of `clr`, halved). -/
noncomputable def dclr (hs hc : ℝ) (P Q : Mov) : ℝ :=
  (Q.x 0 - P.x 0) * (Q.x' - P.x') + (Q.y 0 - P.y 0) * (Q.y' - P.y') -
    (hs * (P.x 0 + Q.x 0) + hc * (P.y 0 + Q.y 0)) / 2

theorem clr_deriv (hs hc : ℝ) (P Q : Mov) : HasDerivAt (clr hs hc P Q) (2 * dclr hs hc P Q) 0 := by
  have hL := ((Q.hx.sub P.hx).pow 2).add ((Q.hy.sub P.hy).pow 2)
  have hR := ((((hasDerivAt_id (0 : ℝ)).mul
    (((P.hx.add Q.hx).const_mul hs).add ((P.hy.add Q.hy).const_mul hc))).div_const 2).const_add
      1).pow 2
  have h := hL.sub hR
  convert h using 1
  · funext t
    simp only [clr, Pi.add_apply, Pi.sub_apply, Pi.pow_apply, Pi.mul_apply, id]
  · simp only [dclr, Pi.add_apply, Pi.sub_apply, Pi.mul_apply, id]
    norm_num
    ring

theorem clr_zero {hs hc : ℝ} {P Q : Mov} (h : (Q.x 0 - P.x 0) ^ 2 + (Q.y 0 - P.y 0) ^ 2 = 1) :
    clr hs hc P Q 0 = 0 := by
  simp [clr, h]

/-- A function vanishing at `0` with positive derivative is positive just to the right of `0`. -/
theorem eventually_pos_of_deriv {g : ℝ → ℝ} {g' : ℝ} (hg : HasDerivAt g g' 0) (h0 : g 0 = 0)
    (hpos : 0 < g') : ∀ᶠ t in 𝓝[>] (0 : ℝ), 0 < g t := by
  have hT := hg.tendsto_slope_zero_right
  simp only [zero_add, h0, sub_zero, smul_eq_mul] at hT
  filter_upwards [hT.eventually (lt_mem_nhds hpos), self_mem_nhdsWithin] with t h1 ht
  have ht' : (0 : ℝ) < t := ht
  have : g t = t * (t⁻¹ * g t) := by field_simp
  rw [this]
  positivity

theorem eventually_neg_of_deriv {g : ℝ → ℝ} {g' : ℝ} (hg : HasDerivAt g g' 0) (h0 : g 0 = 0)
    (hneg : g' < 0) : ∀ᶠ t in 𝓝[>] (0 : ℝ), g t < 0 := by
  have := eventually_pos_of_deriv hg.neg (by simp [h0]) (by linarith)
  filter_upwards [this] with t ht
  simpa using ht

/-! ## Hinge rates -/

/-- The rate of a hinge, from the derivative of the relative angle of two front vectors. -/
theorem hinge_rate {F G : ℝ → ℂ} {F' G' : ℂ} {r : ℝ} (hF : HasDerivAt F F' 0)
    (hG : HasDerivAt G G' 0) (h0 : F 0 = G 0) (hne : G 0 ≠ 0)
    (h : HasDerivAt (fun t => arg (F t / G t)) r 0) : ((F' - G') / G 0).im = r :=
  (ratio_arg_deriv hF hG h0 hne).unique h

/-! ## The perturbed front -/

/-- Five consecutive front disks `Z, A, B, C, E` near the notch-60 lattice (rotated frame), touching
for all small `t` with diameters `1 + t k H`, and hinge rates `α` (at `A`), `σ` (notch at `B`), `-ε`
(at `C`). -/
structure Front (α σ ε k Wr Wi : ℝ) where
  Z : Mov
  A : Mov
  B : Mov
  C : Mov
  E : Mov
  hZ : Z.x 0 = 1 ∧ Z.y 0 = √3
  hA : A.x 0 = 1 / 2 ∧ A.y 0 = √3 / 2
  hB : B.x 0 = 0 ∧ B.y 0 = 0
  hC : C.x 0 = 1 ∧ C.y 0 = 0
  hE : E.x 0 = 2 ∧ E.y 0 = 0
  tZA : Tan 1 (k * Wi) (k * Wr) Z A
  tAB : Tan 1 (k * Wi) (k * Wr) A B
  tBC : Tan 1 (k * Wi) (k * Wr) B C
  tCE : Tan 1 (k * Wi) (k * Wr) C E
  hα : HasDerivAt (fun t => arg ((A.pos t - Z.pos t) / (B.pos t - A.pos t))) α 0
  hσ : HasDerivAt (fun t => arg ((B.pos t - A.pos t) / (-ω * (C.pos t - B.pos t)))) σ 0
  hε : HasDerivAt (fun t => arg ((C.pos t - B.pos t) / (E.pos t - C.pos t))) (-ε) 0

/-- The pentagon margin against `C` (`> 0` iff the pentagon disk clears `C`). -/
noncomputable def Pm (_α σ ε k Wr Wi : ℝ) : ℝ :=
  √3 / 2 * (ε - σ) + k * (3 * Wi + 5 * √3 * Wr) / 8

/-- The channel margin (`> 0` iff the pentagon disk clears `Z`, iff `Z` and `E` are apart). -/
noncomputable def Rm (α σ ε k Wr Wi : ℝ) : ℝ :=
  √3 / 2 * (2 * σ + α - ε) - k * (3 * Wi + √3 * Wr) / 2

section
variable {α σ ε k Wr Wi : ℝ}

/-- The seven first-order front equations: four tangencies and three hinge rates. -/
theorem Front.eqs (F : Front α σ ε k Wr Wi) :
    (1 / 2 - 1) * (F.A.x' - F.Z.x') + (√3 / 2 - √3) * (F.A.y' - F.Z.y') =
        1 * (k * Wi * (1 + 1 / 2) + k * Wr * (√3 + √3 / 2)) / 2 ∧
      (0 - 1 / 2) * (F.B.x' - F.A.x') + (0 - √3 / 2) * (F.B.y' - F.A.y') =
        1 * (k * Wi * (1 / 2 + 0) + k * Wr * (√3 / 2 + 0)) / 2 ∧
      (1 - 0) * (F.C.x' - F.B.x') + (0 - 0) * (F.C.y' - F.B.y') =
        1 * (k * Wi * (0 + 1) + k * Wr * (0 + 0)) / 2 ∧
      (2 - 1) * (F.E.x' - F.C.x') + (0 - 0) * (F.E.y' - F.C.y') =
        1 * (k * Wi * (1 + 2) + k * Wr * (0 + 0)) / 2 ∧
      -(F.A.y' - F.Z.y' - (F.B.y' - F.A.y')) / 2 + √3 / 2 * (F.A.x' - F.Z.x' - (F.B.x' - F.A.x')) =
        α ∧
      -((F.B.y' - F.A.y') + (1 / 2 * (F.C.y' - F.B.y') + √3 / 2 * (F.C.x' - F.B.x'))) / 2 +
          √3 / 2 * ((F.B.x' - F.A.x') + (1 / 2 * (F.C.x' - F.B.x') - √3 / 2 * (F.C.y' - F.B.y'))) =
        σ ∧
      (F.C.y' - F.B.y') - (F.E.y' - F.C.y') = -ε := by
  have h3 : √3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  obtain ⟨hZx, hZy⟩ := F.hZ
  obtain ⟨hAx, hAy⟩ := F.hA
  obtain ⟨hBx, hBy⟩ := F.hB
  obtain ⟨hCx, hCy⟩ := F.hC
  obtain ⟨hEx, hEy⟩ := F.hE
  have t1 := tangency_deriv F.tZA
  have t2 := tangency_deriv F.tAB
  have t3 := tangency_deriv F.tBC
  have t4 := tangency_deriv F.tCE
  rw [hZx, hZy, hAx, hAy] at t1
  rw [hAx, hAy, hBx, hBy] at t2
  rw [hBx, hBy, hCx, hCy] at t3
  rw [hCx, hCy, hEx, hEy] at t4
  have pZ : F.Z.pos 0 = ⟨1, √3⟩ := by apply Complex.ext <;> simp [Mov.pos, hZx, hZy]
  have pA : F.A.pos 0 = ⟨1 / 2, √3 / 2⟩ := by apply Complex.ext <;> simp [Mov.pos, hAx, hAy]
  have pB : F.B.pos 0 = 0 := by apply Complex.ext <;> simp [Mov.pos, hBx, hBy]
  have pC : F.C.pos 0 = 1 := by apply Complex.ext <;> simp [Mov.pos, hCx, hCy]
  have pE : F.E.pos 0 = 2 := by apply Complex.ext <;> simp [Mov.pos, hEx, hEy]
  have nω : Complex.normSq (⟨-1 / 2, -√3 / 2⟩ : ℂ) = 1 := by
    rw [Complex.normSq_mk]
    linear_combination (1 / 4) * h3
  -- hinge at A
  have gA : F.B.pos 0 - F.A.pos 0 = ⟨-1 / 2, -√3 / 2⟩ := by
    rw [pA, pB]; apply Complex.ext <;> simp <;> ring
  have dZA : HasDerivAt (fun t => F.A.pos t - F.Z.pos t) (F.A.vel - F.Z.vel) 0 :=
    (F.A.hasDerivAt_pos).sub (F.Z.hasDerivAt_pos)
  have dAB : HasDerivAt (fun t => F.B.pos t - F.A.pos t) (F.B.vel - F.A.vel) 0 :=
    (F.B.hasDerivAt_pos).sub (F.A.hasDerivAt_pos)
  have eA := hinge_rate dZA dAB
    (by show F.A.pos 0 - F.Z.pos 0 = F.B.pos 0 - F.A.pos 0
        rw [pZ, pA, pB]; apply Complex.ext <;> simp <;> ring)
    (by show F.B.pos 0 - F.A.pos 0 ≠ 0
        rw [gA]; intro h; have := congrArg Complex.re h; simp at this) F.hα
  change ((F.A.vel - F.Z.vel - (F.B.vel - F.A.vel)) / (F.B.pos 0 - F.A.pos 0)).im = α at eA
  rw [gA, Complex.div_im, nω] at eA
  simp only [Mov.vel, Complex.sub_re, Complex.sub_im, div_one] at eA
  -- hinge at B
  have gB : -ω * (F.C.pos 0 - F.B.pos 0) = ⟨-1 / 2, -√3 / 2⟩ := by
    rw [pB, pC]; apply Complex.ext <;> simp [ω] <;> ring
  have dBC : HasDerivAt (fun t => -ω * (F.C.pos t - F.B.pos t)) (-ω * (F.C.vel - F.B.vel)) 0 :=
    ((F.C.hasDerivAt_pos).sub (F.B.hasDerivAt_pos)).const_mul (-ω)
  have eB := hinge_rate dAB dBC
    (by show F.B.pos 0 - F.A.pos 0 = -ω * (F.C.pos 0 - F.B.pos 0)
        rw [gB, gA])
    (by show -ω * (F.C.pos 0 - F.B.pos 0) ≠ 0
        rw [gB]; intro h; have := congrArg Complex.re h; simp at this) F.hσ
  change ((F.B.vel - F.A.vel - -ω * (F.C.vel - F.B.vel)) / (-ω * (F.C.pos 0 - F.B.pos 0))).im = σ
    at eB
  rw [gB, Complex.div_im, nω] at eB
  simp only [Mov.vel, ω, Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im,
    Complex.neg_re, Complex.neg_im, div_one] at eB
  -- hinge at C
  have gC : F.E.pos 0 - F.C.pos 0 = 1 := by rw [pC, pE]; norm_num
  have dCE : HasDerivAt (fun t => F.E.pos t - F.C.pos t) (F.E.vel - F.C.vel) 0 :=
    (F.E.hasDerivAt_pos).sub (F.C.hasDerivAt_pos)
  have dBC' : HasDerivAt (fun t => F.C.pos t - F.B.pos t) (F.C.vel - F.B.vel) 0 :=
    (F.C.hasDerivAt_pos).sub (F.B.hasDerivAt_pos)
  have eC := hinge_rate dBC' dCE
    (by show F.C.pos 0 - F.B.pos 0 = F.E.pos 0 - F.C.pos 0
        rw [gC, pB, pC]; norm_num)
    (by show F.E.pos 0 - F.C.pos 0 ≠ 0
        rw [gC]; exact one_ne_zero) F.hε
  change ((F.C.vel - F.B.vel - (F.E.vel - F.C.vel)) / (F.E.pos 0 - F.C.pos 0)).im = -ε at eC
  rw [gC, div_one] at eC
  simp only [Mov.vel, Complex.sub_im] at eC
  refine ⟨by linear_combination t1, by linear_combination t2, by linear_combination t3,
    by linear_combination t4, by linear_combination eA, by linear_combination eB,
    by linear_combination eC⟩

/-- The first-order equations of a disk `Q` at `Q0 = (3/2, √3/2)` touching `P`. -/
theorem apex_eq {P Q : Mov} {px py : ℝ} (hP : P.x 0 = px ∧ P.y 0 = py)
    (hQ : Q.x 0 = 3 / 2 ∧ Q.y 0 = √3 / 2) (h : Tan 1 (k * Wi) (k * Wr) P Q) :
    (3 / 2 - px) * (Q.x' - P.x') + (√3 / 2 - py) * (Q.y' - P.y') =
      1 * (k * Wi * (px + 3 / 2) + k * Wr * (py + √3 / 2)) / 2 := by
  have t := tangency_deriv h
  rw [hP.1, hP.2, hQ.1, hQ.2] at t
  exact t

theorem apex_eq' {P Q : Mov} {px py : ℝ} (hP : P.x 0 = px ∧ P.y 0 = py)
    (hQ : Q.x 0 = 3 / 2 ∧ Q.y 0 = √3 / 2) (h : Tan 1 (k * Wi) (k * Wr) Q P) :
    (px - 3 / 2) * (P.x' - Q.x') + (py - √3 / 2) * (P.y' - Q.y') =
      1 * (k * Wi * (3 / 2 + px) + k * Wr * (√3 / 2 + py)) / 2 := by
  have t := tangency_deriv h
  rw [hP.1, hP.2, hQ.1, hQ.2] at t
  exact t

/-! ## First-order clearances of the six candidates at `Q0` -/

/-- **The pentagon clears `C`** at first order `P`. -/
theorem pentagon_clear_C (F : Front α σ ε k Wr Wi) (Q : Mov) (hQ : Q.x 0 = 3 / 2 ∧ Q.y 0 = √3 / 2)
    (tAQ : Tan 1 (k * Wi) (k * Wr) F.A Q) (tQE : Tan 1 (k * Wi) (k * Wr) Q F.E) :
    HasDerivAt (clr (k * Wi) (k * Wr) F.C Q) (2 * Pm α σ ε k Wr Wi) 0 := by
  have h3 : √3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  obtain ⟨tZA, tAB, tBC, tCE, eA, eB, eC⟩ := F.eqs
  have tAQ' := apex_eq F.hA hQ tAQ
  have tQE' := apex_eq' F.hE hQ tQE
  convert clr_deriv (k * Wi) (k * Wr) F.C Q using 2
  unfold dclr Pm
  rw [F.hC.1, F.hC.2, hQ.1, hQ.2]
  linear_combination (-1) * ((1 / 2) * tAB + (-1) * tBC + (-1 / 2) * tCE + tAQ' + tQE' +
    (-√3 / 2) * eB + (-√3 / 2) * eC +
    (-F.A.x' / 4 + F.B.x' / 4 + √3 * (F.B.y' / 8 - F.C.y' / 8)) * h3)


/-- **The pentagon clears `Z`** at first order `R` (the channel margin). -/
theorem pentagon_clear_Z (F : Front α σ ε k Wr Wi) (Q : Mov) (hQ : Q.x 0 = 3 / 2 ∧ Q.y 0 = √3 / 2)
    (tQE : Tan 1 (k * Wi) (k * Wr) Q F.E) :
    HasDerivAt (clr (k * Wi) (k * Wr) F.Z Q) (2 * Rm α σ ε k Wr Wi) 0 := by
  have h3 : √3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  obtain ⟨tZA, tAB, tBC, tCE, eA, eB, eC⟩ := F.eqs
  have tQE' := apex_eq' F.hE hQ tQE
  convert clr_deriv (k * Wi) (k * Wr) F.Z Q using 2
  unfold dclr Rm
  rw [F.hZ.1, F.hZ.2, hQ.1, hQ.2]
  linear_combination (-1) * ((1 / 2) * tZA + (1 / 2) * tAB + (1 / 2) * tBC + (1 / 2) * tCE +
    (-1) * tQE' + (√3 / 2) * eA + √3 * eB + (√3 / 2) * eC +
    (-F.B.x' / 4 + F.Z.x' / 4 + √3 * (-F.B.y' / 4 + F.C.y' / 4)) * h3)

/-- **The rhombus is blocked**: the disk touching `A` and `C` overlaps `E` at rate `-2P`. -/
theorem rhombus_hits_E (F : Front α σ ε k Wr Wi) (Q : Mov) (hQ : Q.x 0 = 3 / 2 ∧ Q.y 0 = √3 / 2)
    (tAQ : Tan 1 (k * Wi) (k * Wr) F.A Q) (tQC : Tan 1 (k * Wi) (k * Wr) Q F.C) :
    HasDerivAt (clr (k * Wi) (k * Wr) F.E Q) (2 * -Pm α σ ε k Wr Wi) 0 := by
  have h3 : √3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  obtain ⟨tZA, tAB, tBC, tCE, eA, eB, eC⟩ := F.eqs
  have tAQ' := apex_eq F.hA hQ tAQ
  have tQC' := apex_eq' F.hC hQ tQC
  convert clr_deriv (k * Wi) (k * Wr) F.E Q using 2
  unfold dclr Pm
  rw [F.hE.1, F.hE.2, hQ.1, hQ.2]
  linear_combination (-1) * ((-1 / 2) * tAB + tBC + (1 / 2) * tCE + (-1) * tAQ' + tQC' +
    (√3 / 2) * eB + (√3 / 2) * eC +
    (F.A.x' / 4 - F.B.x' / 4 + √3 * (-F.B.y' / 8 + F.C.y' / 8)) * h3)

/-- **The triangle on `U₂` is blocked**: the disk touching `C` and `E` overlaps `A` at rate `-2P`.
-/
theorem triangle_hits_A (F : Front α σ ε k Wr Wi) (Q : Mov) (hQ : Q.x 0 = 3 / 2 ∧ Q.y 0 = √3 / 2)
    (tCQ : Tan 1 (k * Wi) (k * Wr) F.C Q) (tQE : Tan 1 (k * Wi) (k * Wr) Q F.E) :
    HasDerivAt (clr (k * Wi) (k * Wr) F.A Q) (2 * -Pm α σ ε k Wr Wi) 0 := by
  have h3 : √3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  obtain ⟨tZA, tAB, tBC, tCE, eA, eB, eC⟩ := F.eqs
  have tCQ' := apex_eq F.hC hQ tCQ
  have tQE' := apex_eq' F.hE hQ tQE
  convert clr_deriv (k * Wi) (k * Wr) F.A Q using 2
  unfold dclr Pm
  rw [F.hA.1, F.hA.2, hQ.1, hQ.2]
  linear_combination (-1) * ((-1 / 2) * tAB + tBC + (1 / 2) * tCE + tCQ' + (-1) * tQE' +
    (√3 / 2) * eB + (√3 / 2) * eC +
    (F.A.x' / 4 - F.B.x' / 4 + √3 * (-F.B.y' / 8 + F.C.y' / 8)) * h3)

/-- **The disk touching `Z` and `C` is blocked**: it overlaps `A` at rate `-2(P + R)`. -/
theorem zc_hits_A (F : Front α σ ε k Wr Wi) (Q : Mov) (hQ : Q.x 0 = 3 / 2 ∧ Q.y 0 = √3 / 2)
    (tZQ : Tan 1 (k * Wi) (k * Wr) F.Z Q) (tQC : Tan 1 (k * Wi) (k * Wr) Q F.C) :
    HasDerivAt (clr (k * Wi) (k * Wr) F.A Q) (2 * -(Pm α σ ε k Wr Wi + Rm α σ ε k Wr Wi)) 0 := by
  have h3 : √3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  obtain ⟨tZA, tAB, tBC, tCE, eA, eB, eC⟩ := F.eqs
  have tZQ' := apex_eq F.hZ hQ tZQ
  have tQC' := apex_eq' F.hC hQ tQC
  convert clr_deriv (k * Wi) (k * Wr) F.A Q using 2
  unfold dclr Pm Rm
  rw [F.hA.1, F.hA.2, hQ.1, hQ.2]
  linear_combination (-1) * ((-1 / 2) * tZA + (-1) * tAB + (1 / 2) * tBC + tZQ' + tQC' +
    (-√3 / 2) * eA + (-√3 / 2) * eB +
    (F.A.x' / 4 - F.Z.x' / 4 + √3 * (F.B.y' / 8 - F.C.y' / 8)) * h3)

/-- **The disk touching `Z` and `A` is higher** than the pentagon disk by `(2/√3) R cos u` to first
order (`Wr = cos u`). -/
theorem za_higher (F : Front α σ ε k Wr Wi) (Q V : Mov) (hQ : Q.x 0 = 3 / 2 ∧ Q.y 0 = √3 / 2)
    (hV : V.x 0 = 3 / 2 ∧ V.y 0 = √3 / 2)
    (tAQ : Tan 1 (k * Wi) (k * Wr) F.A Q) (tQE : Tan 1 (k * Wi) (k * Wr) Q F.E)
    (tZV : Tan 1 (k * Wi) (k * Wr) F.Z V) (tVA : Tan 1 (k * Wi) (k * Wr) V F.A) :
    √3 * (Wi * (V.x' - Q.x') + Wr * (V.y' - Q.y')) = 2 * Rm α σ ε k Wr Wi * Wr := by
  have h3 : √3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  obtain ⟨tZA, tAB, tBC, tCE, eA, eB, eC⟩ := F.eqs
  have tAQ' := apex_eq F.hA hQ tAQ
  have tQE' := apex_eq' F.hE hQ tQE
  have tZV' := apex_eq F.hZ hV tZV
  have tVA' := apex_eq' F.hA hV tVA
  unfold Rm
  linear_combination Wr * tZA + Wr * tAB + Wr * tBC + Wr * tCE + (-Wi * √3 - Wr) * tAQ' +
    (-2 * Wr) * tQE' + (-2 * Wr) * tZV' + (Wi * √3 + Wr) * tVA' + (Wr * √3) * eA +
    (2 * Wr * √3) * eB + (Wr * √3) * eC +
    (-F.B.x' * Wr / 2 + Wr * F.Z.x' / 2 + √3 * (-F.B.y' * Wr / 2 + F.C.y' * Wr / 2)) * h3

/-- **The channel.** `Z` and `E` are two diameters apart at `t = 0`; the excess of half their
distance over the diameters of a disk between them (at the height of `Q0`) grows at rate `R`. -/
theorem channel_rate (F : Front α σ ε k Wr Wi) :
    ((2 - 1) * (F.E.x' - F.Z.x') + (0 - √3) * (F.E.y' - F.Z.y')) / 2 -
        k * ((Wi * 1 + Wr * √3 + (Wi * 2 + Wr * 0)) / 2 + (Wi * (3 / 2) + Wr * (√3 / 2))) =
      Rm α σ ε k Wr Wi := by
  have h3 : √3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  obtain ⟨tZA, tAB, tBC, tCE, eA, eB, eC⟩ := F.eqs
  unfold Rm
  linear_combination (1 / 2) * tZA + (1 / 2) * tAB + (1 / 2) * tBC + (1 / 2) * tCE +
    (√3 / 2) * eA + √3 * eB + (√3 / 2) * eC +
    (-F.B.x' / 4 + F.Z.x' / 4 + √3 * (-F.B.y' / 4 + F.C.y' / 4)) * h3

end

/-! ## Validity and the channel -/

/-- **Validity at the notch.** `A` and `C` are at unit distance at `t = 0`; their clearance grows at
rate `(√3/2) σ - k (√3 Wr + 3 Wi)/8`, that is `(√3/2)(σ - (k/2) cos(u - 60°))`. -/
theorem notch_clear {α σ ε k Wr Wi : ℝ} (F : Front α σ ε k Wr Wi) :
    HasDerivAt (clr (k * Wi) (k * Wr) F.A F.C)
      (2 * (√3 / 2 * σ - k * (√3 * Wr + 3 * Wi) / 8)) 0 := by
  have h3 : √3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  obtain ⟨tZA, tAB, tBC, tCE, eA, eB, eC⟩ := F.eqs
  convert clr_deriv (k * Wi) (k * Wr) F.A F.C using 2
  unfold dclr
  rw [F.hA.1, F.hA.2, F.hC.1, F.hC.2]
  linear_combination (-1) * ((1 / 2) * tAB + (1 / 2) * tBC + (√3 / 2) * eB +
    (F.A.x' / 4 - F.B.x' / 4 + √3 * (-F.B.y' / 8 + F.C.y' / 8)) * h3)

/-- The first-order clearance at the ridge, `(√3/2)(α + σ - ε - (q/2) cos(u - 60°))` with `k = -q`
(computed by hand in the paper: the ridge is not one of the five local disks). -/
noncomputable def Gm (α σ ε k Wr Wi : ℝ) : ℝ :=
  √3 / 2 * (α + σ - ε) + k * (√3 * Wr + 3 * Wi) / 8

/-- **The channel opens on every valid front.** `R` is the notch clearance plus the ridge clearance
plus `-k (3 sin u + √3 cos u)/2 ≥ 0`. -/
theorem Rm_eq (α σ ε k Wr Wi : ℝ) :
    Rm α σ ε k Wr Wi = (√3 / 2 * σ - k * (√3 * Wr + 3 * Wi) / 8) + Gm α σ ε k Wr Wi -
      k * (3 * Wi + √3 * Wr) / 2 := by
  unfold Rm Gm
  ring

theorem channel_of_valid {α σ ε k Wr Wi : ℝ} (hk : k ≤ 0) (hW : 0 ≤ 3 * Wi + √3 * Wr)
    (hN : 0 < √3 / 2 * σ - k * (√3 * Wr + 3 * Wi) / 8) (hG : 0 < Gm α σ ε k Wr Wi) :
    0 < Rm α σ ε k Wr Wi := by
  rw [Rm_eq]
  have : 0 ≤ -k * (3 * Wi + √3 * Wr) := mul_nonneg (by linarith) hW
  linarith

/-! ## The window -/

/-- **The window.** For `k ≤ 0` (shrinking disks), with `W = e^{iu}`, both margins are positive iff
`(ε - α)/2 - |k| (√3 sin u + cos u)/2 < σ < ε - |k| (√3 sin u + 5 cos u)/4`. -/
theorem window_iff {α σ ε k u : ℝ} (hk : k ≤ 0) :
    (0 < Pm α σ ε k (Real.cos u) (Real.sin u) ∧ 0 < Rm α σ ε k (Real.cos u) (Real.sin u)) ↔
      ((ε - α) / 2 - |k| * (√3 * Real.sin u + Real.cos u) / 2 < σ ∧
        σ < ε - |k| * (√3 * Real.sin u + 5 * Real.cos u) / 4) := by
  have h3 : √3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have s3 : (0 : ℝ) < √3 := by positivity
  rw [abs_of_nonpos hk]
  have hP : Pm α σ ε k (Real.cos u) (Real.sin u) =
      √3 / 2 * ((ε - -k * (√3 * Real.sin u + 5 * Real.cos u) / 4) - σ) := by
    unfold Pm
    linear_combination (-(k * Real.sin u) / 8) * h3
  have hR : Rm α σ ε k (Real.cos u) (Real.sin u) =
      √3 * (σ - ((ε - α) / 2 - -k * (√3 * Real.sin u + Real.cos u) / 2)) := by
    unfold Rm
    linear_combination (k * Real.sin u / 2) * h3
  rw [hP, hR, mul_pos_iff_of_pos_left (by positivity), mul_pos_iff_of_pos_left s3, sub_pos,
    sub_pos]
  exact And.comm

/-! ## Theorem C (first order) -/

/-- **Theorem C, first-order form.** On the window, for all small `t > 0`: the pentagon disk
(touching `A` and `E`) is clear of `C` and `Z`, while the disks touching `A, C` (rhombus), `C, E`
(triangle) and `Z, C` overlap `E`, `A`, `A`. (With `za_higher` and `channel_rate`: the pentagon is
the lowest free position at `Q0`.) -/
theorem pentagon_first {α σ ε k Wr Wi : ℝ} (F : Front α σ ε k Wr Wi)
    (hPm : 0 < Pm α σ ε k Wr Wi) (hRm : 0 < Rm α σ ε k Wr Wi)
    (Q Qr Qt Qw : Mov) (hQ : Q.x 0 = 3 / 2 ∧ Q.y 0 = √3 / 2)
    (hQr : Qr.x 0 = 3 / 2 ∧ Qr.y 0 = √3 / 2)
    (hQt : Qt.x 0 = 3 / 2 ∧ Qt.y 0 = √3 / 2) (hQw : Qw.x 0 = 3 / 2 ∧ Qw.y 0 = √3 / 2)
    (tAQ : Tan 1 (k * Wi) (k * Wr) F.A Q) (tQE : Tan 1 (k * Wi) (k * Wr) Q F.E)
    (tAQr : Tan 1 (k * Wi) (k * Wr) F.A Qr) (tQrC : Tan 1 (k * Wi) (k * Wr) Qr F.C)
    (tCQt : Tan 1 (k * Wi) (k * Wr) F.C Qt) (tQtE : Tan 1 (k * Wi) (k * Wr) Qt F.E)
    (tZQw : Tan 1 (k * Wi) (k * Wr) F.Z Qw) (tQwC : Tan 1 (k * Wi) (k * Wr) Qw F.C) :
    ∀ᶠ t in 𝓝[>] (0 : ℝ),
      0 < clr (k * Wi) (k * Wr) F.C Q t ∧ 0 < clr (k * Wi) (k * Wr) F.Z Q t ∧
        clr (k * Wi) (k * Wr) F.E Qr t < 0 ∧ clr (k * Wi) (k * Wr) F.A Qt t < 0 ∧
          clr (k * Wi) (k * Wr) F.A Qw t < 0 := by
  have h3 : √3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have z1 : ∀ {P X : Mov} {px py : ℝ}, (P.x 0 = px ∧ P.y 0 = py) →
      (X.x 0 = 3 / 2 ∧ X.y 0 = √3 / 2) → (3 / 2 - px) ^ 2 + (√3 / 2 - py) ^ 2 = 1 →
        clr (k * Wi) (k * Wr) P X 0 = 0 := by
    intro P X px py hP hX h
    exact clr_zero (by rw [hP.1, hP.2, hX.1, hX.2]; exact h)
  have dC : (3 / 2 - 1 : ℝ) ^ 2 + (√3 / 2 - 0) ^ 2 = 1 := by linear_combination (1 / 4) * h3
  have dZ : (3 / 2 - 1 : ℝ) ^ 2 + (√3 / 2 - √3) ^ 2 = 1 := by linear_combination (1 / 4) * h3
  have dE : (3 / 2 - 2 : ℝ) ^ 2 + (√3 / 2 - 0) ^ 2 = 1 := by linear_combination (1 / 4) * h3
  have dA : (3 / 2 - 1 / 2 : ℝ) ^ 2 + (√3 / 2 - √3 / 2) ^ 2 = 1 := by ring
  have e1 := eventually_pos_of_deriv (pentagon_clear_C F Q hQ tAQ tQE) (z1 F.hC hQ dC)
    (by linarith)
  have e2 := eventually_pos_of_deriv (pentagon_clear_Z F Q hQ tQE) (z1 F.hZ hQ dZ) (by linarith)
  have e3 := eventually_neg_of_deriv (rhombus_hits_E F Qr hQr tAQr tQrC) (z1 F.hE hQr dE)
    (by linarith)
  have e4 := eventually_neg_of_deriv (triangle_hits_A F Qt hQt tCQt tQtE) (z1 F.hA hQt dA)
    (by linarith)
  have e5 := eventually_neg_of_deriv (zc_hits_A F Qw hQw tZQw tQwC) (z1 F.hA hQw dA)
    (by linarith)
  filter_upwards [e1, e2, e3, e4, e5] with t h1 h2 h3' h4 h5
  exact ⟨h1, h2, h3', h4, h5⟩

end Phyllotaxis.Static
