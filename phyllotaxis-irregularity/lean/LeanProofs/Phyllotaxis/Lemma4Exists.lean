import LeanProofs.Phyllotaxis.Apex
import LeanProofs.Phyllotaxis.Lemma4

/-!
# Lemma 4 is not vacuous

Explicit families satisfying every hypothesis of `Lemma4.dG_dc` (for every height direction
`(s, k)`) and
of `Lemma4.dG_dθ`: the notch `P0 P1 P2 P3` with fixed hinge directions and lengths equal to mean
diameters
(closed forms `L = 1/(1 - c s/2)` etc.), and the pentagon disk `Q` from the implicit function
theorem
(`Apex.apex_mov`).
-/

namespace Phyllotaxis.Lemma4Exists

open Filter Topology Phyllotaxis.FirstOrder Phyllotaxis.Apex

/-- `1/(1 - c a)` and `(1 + c b)/(1 - c a)` are `C¹` at `0`. -/
theorem frac_contDiffAt (a b : ℝ) :
    ContDiffAt ℝ 1 (fun c : ℝ => (1 + c * b) / (1 - c * a)) 0 :=
  (contDiffAt_const.add (contDiffAt_id.mul contDiffAt_const)).div
    (contDiffAt_const.sub (contDiffAt_id.mul contDiffAt_const)) (by simp)

theorem eventually_den (a : ℝ) : ∀ᶠ c in 𝓝 (0 : ℝ), 1 - c * a ≠ 0 := by
  have hc : ContinuousAt (fun c : ℝ => 1 - c * a) 0 := by fun_prop
  exact hc.eventually_ne (by simp)

theorem deriv_zero_of_const {f : ℝ → ℝ} (h : ∀ c, f c = 0) : deriv f 0 = 0 := by
  have : f = fun _ => 0 := funext h
  rw [this, deriv_const]

/-- **`dG_dc` is not vacuous.** -/
theorem dG_dc_family (s k : ℝ) :
    ∃ P0 P1 P2 P3 Q : Mov, Tan 1 s k P0 P1 ∧ Tan 1 s k P1 P2 ∧ Tan 1 s k P2 P3 ∧
      Tan 1 s k P0 Q ∧ Tan 1 s k Q P3 ∧ P1.x 0 = 0 ∧ P1.y 0 = 0 ∧ (P1.x' = 0 ∧ P1.y' = 0) ∧
      (P2.x 0 = 1 ∧ P2.y 0 = 0) ∧ (P3.x 0 = 2 ∧ P3.y 0 = 0) ∧
      (P0.x 0 = 1 / 2 ∧ P0.y 0 = √3 / 2) ∧ (Q.x 0 = 3 / 2 ∧ Q.y 0 = √3 / 2) ∧
      P2.y' = 0 ∧ P3.y' = 0 ∧ P0.y' = √3 * P0.x' := by
  have h3 : √3 * √3 = 3 := Real.mul_self_sqrt (by norm_num)
  set t := s / 2 + √3 / 2 * k
  -- lengths: L12 = 1/(1 - cs/2), L23 = (1 + c s L12)/(1 - cs/2), L01 = 1/(1 - ct/2)
  set L12 : ℝ → ℝ := fun c => (1 + c * 0) / (1 - c * (s / 2))
  set L23 : ℝ → ℝ := fun c => (1 + c * (s * L12 c)) / (1 - c * (s / 2))
  set L01 : ℝ → ℝ := fun c => (1 + c * 0) / (1 - c * (t / 2))
  have h12 : ContDiffAt ℝ 1 L12 0 := frac_contDiffAt _ _
  have h23 : ContDiffAt ℝ 1 L23 0 :=
    (contDiffAt_const.add (contDiffAt_id.mul (contDiffAt_const.mul h12))).div
      (contDiffAt_const.sub (contDiffAt_id.mul contDiffAt_const)) (by simp)
  have h01 : ContDiffAt ℝ 1 L01 0 := frac_contDiffAt _ _
  set P1 := still 0 0
  set P2 := ofContDiff L12 (fun _ => 0) h12 contDiffAt_const
  set P3 := ofContDiff (fun c => L12 c + L23 c) (fun _ => 0) (h12.add h23) contDiffAt_const
  set P0 := ofContDiff (fun c => L01 c / 2) (fun c => √3 * (L01 c / 2)) (h01.div_const 2)
    (contDiffAt_const.mul (h01.div_const 2))
  have e12 : ∀ᶠ c in 𝓝 (0 : ℝ), L12 c * (1 - c * (s / 2)) = 1 := by
    filter_upwards [eventually_den (s / 2)] with c hc
    simp only [L12]
    rw [div_mul_cancel₀ _ hc]
    ring
  have e23 : ∀ᶠ c in 𝓝 (0 : ℝ), L23 c * (1 - c * (s / 2)) = 1 + c * (s * L12 c) := by
    filter_upwards [eventually_den (s / 2)] with c hc
    simp only [L23]
    rw [div_mul_cancel₀ _ hc]
  have e01 : ∀ᶠ c in 𝓝 (0 : ℝ), L01 c * (1 - c * (t / 2)) = 1 := by
    filter_upwards [eventually_den (t / 2)] with c hc
    simp only [L01]
    rw [div_mul_cancel₀ _ hc]
    ring
  have hT01 : Tan 1 s k P0 P1 := by
    filter_upwards [e01] with c hc
    simp only [P0, P1, still, ofContDiff]
    have : 1 + c * (s * (L01 c / 2 + 0) + k * (√3 * (L01 c / 2) + 0)) / 2 = L01 c := by
      linear_combination -hc
    rw [this]
    linear_combination (L01 c ^ 2 / 4) * h3
  have hT12 : Tan 1 s k P1 P2 := by
    filter_upwards [e12] with c hc
    simp only [P1, P2, still, ofContDiff]
    have : 1 + c * (s * (0 + L12 c) + k * (0 + 0)) / 2 = L12 c := by linear_combination -hc
    rw [this]
    ring
  have hT23 : Tan 1 s k P2 P3 := by
    filter_upwards [e23] with c hc
    simp only [P2, P3, ofContDiff]
    have : 1 + c * (s * (L12 c + (L12 c + L23 c)) + k * (0 + 0)) / 2 = L23 c := by
      linear_combination -hc
    rw [this]
    ring
  have hL0 : L12 0 = 1 ∧ L23 0 = 1 ∧ L01 0 = 1 := by simp [L12, L23, L01]
  obtain ⟨Q, hqx, hqy, hT0Q, hTQ3⟩ := apex_mov (b0 := 1) (hs := s) (hc := k) P0 P3
    (q0 := (3 / 2, √3 / 2)) (h01.div_const 2) (contDiffAt_const.mul (h01.div_const 2))
    (h12.add h23) contDiffAt_const
    (by simp only [P0, ofContDiff, hL0]; linear_combination h3 / 4 * 0 + 0 * h3)
    (by simp only [P3, ofContDiff, hL0]; linear_combination h3 / 4)
    (by
      simp only [P0, P3, ofContDiff, hL0]
      have : 0 < √3 := by positivity
      intro h
      nlinarith)
  refine ⟨P0, P1, P2, P3, Q, hT01, hT12, hT23, hT0Q, hTQ3, rfl, rfl, ⟨rfl, rfl⟩, ?_, ?_, ?_,
    ⟨hqx, hqy⟩, ?_, ?_, ?_⟩
  · simp [P2, ofContDiff, hL0.1]
  · simp only [P3, ofContDiff, hL0]
    norm_num
  · simp only [P0, ofContDiff, hL0]
    exact ⟨by norm_num, by ring⟩
  · exact deriv_zero_of_const fun _ => rfl
  · exact deriv_zero_of_const fun _ => rfl
  · show deriv (fun c => √3 * (L01 c / 2)) 0 = √3 * deriv (fun c => L01 c / 2) 0
    exact deriv_const_mul _ ((h01.div_const 2).differentiableAt one_ne_zero)

/-- **`dG_dθ` is not vacuous.** `U2` turns by `θ` about `P2` (`P3 = (1 + cos θ, sin θ)`), unit
disks. -/
theorem dG_dθ_family :
    ∃ P0 P2 P3 Q : Mov, Tan 1 0 0 P0 Q ∧ Tan 1 0 0 Q P3 ∧
      (P0.x 0 = 1 / 2 ∧ P0.y 0 = √3 / 2) ∧ (P0.x' = 0 ∧ P0.y' = 0) ∧
      (P2.x 0 = 1 ∧ P2.y 0 = 0) ∧ (P2.x' = 0 ∧ P2.y' = 0) ∧
      (P3.x 0 = 2 ∧ P3.y 0 = 0) ∧ (P3.x' = 0 ∧ P3.y' = 1) ∧
      (Q.x 0 = 3 / 2 ∧ Q.y 0 = √3 / 2) := by
  have h3 : √3 * √3 = 3 := Real.mul_self_sqrt (by norm_num)
  have hcx : ContDiffAt ℝ 1 (fun θ : ℝ => 1 + Real.cos θ) 0 :=
    contDiffAt_const.add Real.contDiff_cos.contDiffAt
  have hcy : ContDiffAt ℝ 1 (fun θ : ℝ => Real.sin θ) 0 := Real.contDiff_sin.contDiffAt
  set P0 := still (1 / 2) (√3 / 2)
  set P2 := still 1 0
  set P3 := ofContDiff _ _ hcx hcy
  obtain ⟨Q, hqx, hqy, hT0Q, hTQ3⟩ := apex_mov (b0 := 1) (hs := 0) (hc := 0) P0 P3
    (q0 := (3 / 2, √3 / 2)) contDiffAt_const contDiffAt_const hcx hcy
    (by simp only [P0, still]; norm_num)
    (by simp only [P3, ofContDiff]; simp; linear_combination h3 / 4)
    (by
      simp only [P0, P3, still, ofContDiff]
      simp
      positivity)
  refine ⟨P0, P2, P3, Q, hT0Q, hTQ3, ⟨rfl, rfl⟩, ⟨rfl, rfl⟩, ⟨rfl, rfl⟩, ⟨rfl, rfl⟩, ?_, ?_,
    ⟨hqx, hqy⟩⟩
  · simp only [P3, ofContDiff]
    norm_num
  · simp only [P3, ofContDiff]
    constructor
    · simp
    · simp

end Phyllotaxis.Lemma4Exists
