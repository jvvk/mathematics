import LeanProofs.Phyllotaxis.FirstOrder

/-!
# Lemma 4: local pentagon existence with shrinking disks (the constant `κ₂`)

`open-questions/sunflower-phyllotaxis/PROOF_ratio_law.md`, "Lemma 4". Notch
`P0 -D'-> P1 -U1-> P2 -U2-> P3`
in the frame where `U1` points along the real axis; unit diameters at `P1`, which sits at the
origin at
height `0`; heights are `η(x, y) = s x + k y` with `s = sin α`, `k = cos α`, `α = arg U1` in the
cylinder
frame. The pentagon disk `Q` touches `P0` and `P3`; it is valid while it clears `P2`, measured by
`G = |Q - P2|² - ((d₂ + d_Q)/2)²`. At the degenerate point (`c = 0`, cushion `0`, mismatch `θ = 0`):
`P0 = ω`, `P1 = 0`, `P2 = 1`, `P3 = 2`, `Q = 3/2 + i √3/2`, and `G = 0`.

* `dG_dc`: along the rate, `G'(0) = (5t - s)/2` with `t = sin(α + 60°) = s/2 + (√3/2) k`.
* `dG_dθ`: along the mismatch (`U2` turned by `θ`, `c = 0`), `G'(0) = √3`.
* `kappa2_eq`: `(5t - s)/(2√3) = -(cos β_D + 3√3 sin β_D)/4` when `α = β_D + 120°`.
* `boundary_slope`: the validity boundary `θ*(c)` (where `G = 0`) has slope `-(5t - s)/(2√3)`, so
  for
  `c < 0` it is `θ* = κ₂ |c| + o(c)`.
* `binding_constraint`: at the degenerate point `|Q - P1| = √3 > 1`, so `P2` is the binding disk.
-/

namespace Phyllotaxis.Lemma4

open Filter Topology Real Phyllotaxis.FirstOrder

/-- `G'(c)` along the rate. -/
theorem dG_dc {s k : ℝ} (P0 P1 P2 P3 Q : Mov)
    (h01 : Tan 1 s k P0 P1) (h12 : Tan 1 s k P1 P2) (h23 : Tan 1 s k P2 P3)
    (h0Q : Tan 1 s k P0 Q) (hQ3 : Tan 1 s k Q P3)
    -- base configuration
    (hP1x : P1.x 0 = 0) (hP1y : P1.y 0 = 0) (hP1v : P1.x' = 0 ∧ P1.y' = 0)
    (hP2 : P2.x 0 = 1 ∧ P2.y 0 = 0) (hP3 : P3.x 0 = 2 ∧ P3.y 0 = 0)
    (hP0 : P0.x 0 = 1 / 2 ∧ P0.y 0 = √3 / 2) (hQ : Q.x 0 = 3 / 2 ∧ Q.y 0 = √3 / 2)
    -- hinge angles held fixed: `U1`, `U2` stay horizontal, `D'` keeps direction `ω`
    (hP2y : P2.y' = 0) (hP3y : P3.y' = 0) (hP0d : P0.y' = √3 * P0.x') :
    HasDerivAt (fun c => (Q.x c - P2.x c) ^ 2 + (Q.y c - P2.y c) ^ 2 -
        (1 + c * (s * (P2.x c + Q.x c) + k * (P2.y c + Q.y c)) / 2) ^ 2)
      ((5 * (s / 2 + √3 / 2 * k) - s) / 2) 0 := by
  have h3 : √3 * √3 = 3 := Real.mul_self_sqrt (by norm_num)
  have e01 := tangency_deriv h01
  have e12 := tangency_deriv h12
  have e23 := tangency_deriv h23
  have e0Q := tangency_deriv h0Q
  have eQ3 := tangency_deriv hQ3
  obtain ⟨hv1, hv2⟩ := hP1v
  rw [hP0.1, hP0.2, hP1x, hP1y, hv1, hv2, hP0d] at e01
  rw [hP1x, hP1y, hP2.1, hP2.2, hv1, hv2, hP2y] at e12
  rw [hP2.1, hP2.2, hP3.1, hP3.2, hP2y, hP3y] at e23
  rw [hP0.1, hP0.2, hQ.1, hQ.2, hP0d] at e0Q
  rw [hQ.1, hQ.2, hP3.1, hP3.2, hP3y] at eQ3
  -- solve the chain
  have hx2 : P2.x' = s / 2 := by linarith
  have hx3 : P3.x' = 2 * s := by linarith
  have hx0 : P0.x' = (s / 2 + √3 / 2 * k) / 4 := by linear_combination e01 / 2 - P0.x' / 4 * h3
  have hqx : Q.x' = s / 2 + 5 * (s / 2 + √3 / 2 * k) / 4 := by linear_combination e0Q + hx0
  have hqy : √3 * Q.y' = (6 * s + 9 * (s / 2 + √3 / 2 * k)) / 4 := by
    linear_combination 2 * eQ3 - hx3 + hqx
  -- differentiate G
  have hL := ((Q.hx.sub P2.hx).pow 2).add ((Q.hy.sub P2.hy).pow 2)
  have hR := ((((hasDerivAt_id (0 : ℝ)).mul
    (((P2.hx.add Q.hx).const_mul s).add ((P2.hy.add Q.hy).const_mul k))).div_const 2).const_add
      1).pow 2
  convert hL.sub hR using 1
  · funext c
    simp
  · simp only [Pi.add_apply, Pi.mul_apply, id]
    norm_num
    rw [hP2.1, hP2.2, hQ.1, hQ.2]
    linear_combination -hqx + hx2 - hqy + √3 * hP2y
/-- `G'(θ)` along the mismatch at `c = 0` (constant unit diameters: `Tan 1 0 0`). `P0`, `P2` are
fixed,
`P3` turns with `U2` (velocity `i`), `Q` keeps touching `P0` and `P3`. -/
theorem dG_dθ (P0 P2 P3 Q : Mov) (h0Q : Tan 1 0 0 P0 Q) (hQ3 : Tan 1 0 0 Q P3)
    (hP0 : P0.x 0 = 1 / 2 ∧ P0.y 0 = √3 / 2) (hP0v : P0.x' = 0 ∧ P0.y' = 0)
    (hP2 : P2.x 0 = 1 ∧ P2.y 0 = 0) (hP2v : P2.x' = 0 ∧ P2.y' = 0)
    (hP3 : P3.x 0 = 2 ∧ P3.y 0 = 0) (hP3v : P3.x' = 0 ∧ P3.y' = 1)
    (hQ : Q.x 0 = 3 / 2 ∧ Q.y 0 = √3 / 2) :
    HasDerivAt (fun θ => (Q.x θ - P2.x θ) ^ 2 + (Q.y θ - P2.y θ) ^ 2 - 1) √3 0 := by
  have e0Q := tangency_deriv h0Q
  have eQ3 := tangency_deriv hQ3
  rw [hP0.1, hP0.2, hQ.1, hQ.2, hP0v.1, hP0v.2] at e0Q
  rw [hQ.1, hQ.2, hP3.1, hP3.2, hP3v.1, hP3v.2] at eQ3
  have hL := (((Q.hx.sub P2.hx).pow 2).add ((Q.hy.sub P2.hy).pow 2)).sub_const 1
  convert hL using 1
  simp only [Pi.sub_apply]
  rw [hQ.1, hQ.2, hP2.1, hP2.2, hP2v.1, hP2v.2]
  norm_num
  linear_combination -2 * eQ3 - 2 * e0Q

/-- `κ₂` in terms of the steep down: with `α = β_D + 120°`, `t = sin(α + 60°)`,
`(5t - s)/(2√3) = -(cos β_D + 3√3 sin β_D)/4`. -/
theorem kappa2_eq (β : ℝ) :
    (5 * (Real.sin (β + (π - π / 3)) / 2 + √3 / 2 * Real.cos (β + (π - π / 3))) -
        Real.sin (β + (π - π / 3))) / (2 * √3) =
      -(Real.cos β + 3 * √3 * Real.sin β) / 4 := by
  have h3 : √3 * √3 = 3 := Real.mul_self_sqrt (by norm_num)
  have h3p : 0 < √3 := by positivity
  rw [Real.sin_add, Real.cos_add, Real.sin_pi_sub, Real.cos_pi_sub, Real.sin_pi_div_three,
    Real.cos_pi_div_three]
  rw [div_eq_iff (by positivity)]
  linear_combination Real.sin β / 4 * h3

/-- **Boundary slope.** If `G` is differentiable at `(0, 0)` with `∂G/∂θ = a ≠ 0`, `∂G/∂c = b`, any
differentiable boundary curve `θ*(c)` through `0` with `G(θ*(c), c) = 0` has slope `-b/a`. -/
theorem boundary_slope {G : ℝ × ℝ → ℝ} {L : ℝ × ℝ →L[ℝ] ℝ} (hG : HasFDerivAt G L (0, 0))
    {a b : ℝ} (ha : HasDerivAt (fun θ => G (θ, 0)) a 0) (hb : HasDerivAt (fun c => G (0, c)) b 0)
    (ha0 : a ≠ 0) {θs : ℝ → ℝ} {θ' : ℝ} (hθ : HasDerivAt θs θ' 0) (h0 : θs 0 = 0)
    (hzero : ∀ᶠ c in 𝓝 0, G (θs c, c) = 0) : θ' = -b / a := by
  -- the axis derivatives are the values of `L`
  have hLa : L (1, 0) = a := by
    have hγ : HasDerivAt (fun θ : ℝ => (θ, (0 : ℝ))) (1, 0) 0 :=
      (hasDerivAt_id (0 : ℝ)).prodMk (hasDerivAt_const _ _)
    have := HasFDerivAt.comp_hasDerivAt (f := fun θ : ℝ => (θ, (0 : ℝ))) (0 : ℝ) hG hγ
    exact this.unique ha
  have hLb : L (0, 1) = b := by
    have hγ : HasDerivAt (fun c : ℝ => ((0 : ℝ), c)) (0, 1) 0 :=
      (hasDerivAt_const _ _).prodMk (hasDerivAt_id (0 : ℝ))
    have := HasFDerivAt.comp_hasDerivAt (f := fun c : ℝ => ((0 : ℝ), c)) (0 : ℝ) hG hγ
    exact this.unique hb
  have hγ : HasDerivAt (fun c => (θs c, c)) (θ', 1) 0 := hθ.prodMk (hasDerivAt_id (0 : ℝ))
  have hG' : HasFDerivAt G L ((fun c => (θs c, c)) 0) := by simpa [h0] using hG
  have hcomp := HasFDerivAt.comp_hasDerivAt (f := fun c => (θs c, c)) (0 : ℝ) hG' hγ
  have hz : HasDerivAt (fun c => G (θs c, c)) 0 0 :=
    (hasDerivAt_const (0 : ℝ) (0 : ℝ)).congr_of_eventuallyEq hzero
  have hval := hcomp.unique hz
  have hsplit : ((θ', 1) : ℝ × ℝ) = θ' • ((1 : ℝ), (0 : ℝ)) + ((0 : ℝ), (1 : ℝ)) := by
    ext <;> simp
  rw [hsplit, map_add, map_smul, hLa, hLb, smul_eq_mul] at hval
  field_simp
  linarith

/-- **Lemma 4, assembled.** With the axis derivatives of `dG_dθ` and `dG_dc`, the validity boundary
has
`θ*'(0) = -(5t - s)/(2√3)`; for `c < 0` this is `θ* = κ₂ |c| + o(c)` with `κ₂ = (5t - s)/(2√3)`. -/
theorem kappa2_boundary {s k : ℝ} {G : ℝ × ℝ → ℝ} {L : ℝ × ℝ →L[ℝ] ℝ}
    (hG : HasFDerivAt G L (0, 0)) (hθax : HasDerivAt (fun θ => G (θ, 0)) √3 0)
    (hcax : HasDerivAt (fun c => G (0, c)) ((5 * (s / 2 + √3 / 2 * k) - s) / 2) 0)
    {θs : ℝ → ℝ} {θ' : ℝ} (hθ : HasDerivAt θs θ' 0) (h0 : θs 0 = 0)
    (hzero : ∀ᶠ c in 𝓝 0, G (θs c, c) = 0) :
    θ' = -((5 * (s / 2 + √3 / 2 * k) - s) / (2 * √3)) := by
  rw [boundary_slope hG hθax hcax (by positivity) hθ h0 hzero]
  field_simp

/-- At the degenerate point `|Q - P1| = √3 > 1`: the binding disk is `P2`, not `P1`. -/
theorem binding_constraint : (3 / 2 - 0 : ℝ) ^ 2 + (√3 / 2 - 0) ^ 2 = 3 := by
  have h3 : √3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  linear_combination h3 / 4

/-- `κ₂ = -(cos β + 3√3 sin β)/4` at the `K0` steep child (`cos β = 1/(2√19)`,
`sin β = -5√3/(2√19)`):
`11/(2√19) ≈ 1.2618`. -/
theorem kappa2_K0 {cβ sβ : ℝ} (hc : cβ = 1 / (2 * √19)) (hs : sβ = -(5 * √3) / (2 * √19)) :
    -(cβ + 3 * √3 * sβ) / 4 = 11 / (2 * √19) := by
  have h3 : √3 * √3 = 3 := Real.mul_self_sqrt (by norm_num)
  rw [hc, hs]
  field_simp
  linear_combination (15 : ℝ) * h3

/-- `N = 1` exclusion, exact. Mirrored `DDU` notch at the `(1,2)` threshold: steep down
`β = -(β_U + 60°)` with `cos β = 1/(2√7)`, `sin β = -3√3/(2√7)`, so `κ₂ = 13/(4√7)`; the margin is
`(3/2) cos β_U = 15/(4√7)` on the safe side (`cos β_U = 5/(2√7)`). The pentagon is excluded by
`κ₂ + (3/2) cos β_U = √7` (times `|c|`, at first order). -/
theorem n1_exclusion {cβ sβ cU : ℝ} (hc : cβ = 1 / (2 * √7)) (hs : sβ = -(3 * √3) / (2 * √7))
    (hU : cU = 5 / (2 * √7)) :
    -(cβ + 3 * √3 * sβ) / 4 = 13 / (4 * √7) ∧ 3 / 2 * cU = 15 / (4 * √7) ∧
      -(cβ + 3 * √3 * sβ) / 4 + 3 / 2 * cU = √7 := by
  have h3 : √3 * √3 = 3 := Real.mul_self_sqrt (by norm_num)
  have h7 : √7 * √7 = 7 := Real.mul_self_sqrt (by norm_num)
  have h7p : 0 < √7 := by positivity
  subst hc hs hU
  refine ⟨?_, ?_, ?_⟩
  · field_simp
    linear_combination (9 : ℝ) * h3
  · field_simp
    ring
  · field_simp
    linear_combination 18 * h3 - 16 * h7

end Phyllotaxis.Lemma4
