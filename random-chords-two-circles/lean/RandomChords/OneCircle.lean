import RandomChords.Branches

/-!
# Lemma 1: one circle

For independent uniform points `B = b(cos β, sin β)` and `C = b(cos γ, sin γ)` of a circle about the
origin, the normal angle `φ` of the chord line `BC` and the angle `θ_B` between the normal and the
radius to `B` are independent and uniform on `(0, π)`. So `φ` is uniform and `x_B = cos θ_B` has the
arcsine law, independently of `φ` (Lemma 1).

The paper's proof: as `C` turns at constant speed the chord direction turns at half the speed
(inscribed angle theorem), so `φ` is uniform whatever `B` is, and `x_B = cos (β - φ)`. Here this is
the linear change of variables `(φ, θ) ↦ (β, γ) = (φ + θ, φ - θ)` or `(φ - θ, φ + θ)` (the two
branches, according to the side of the normal on which `B` lies), each with Jacobian `2`.
-/

open Real MeasureTheory Set
open scoped ENNReal

noncomputable section

namespace Chords

/-- `±1` according to the branch. -/
def sgnB (η : Bool) : ℝ := if η then 1 else -1

lemma sgnB_sq (η : Bool) : sgnB η * sgnB η = 1 := by cases η <;> simp [sgnB]

/-- The inverse branches of Lemma 1, as linear maps. -/
def L1 (η : Bool) : ℝ × ℝ →L[ℝ] ℝ × ℝ :=
  ((1 : ℝ) • ContinuousLinearMap.fst ℝ ℝ ℝ + sgnB η • ContinuousLinearMap.snd ℝ ℝ ℝ).prod
    ((1 : ℝ) • ContinuousLinearMap.fst ℝ ℝ ℝ + (-sgnB η) • ContinuousLinearMap.snd ℝ ℝ ℝ)

lemma L1_apply (η : Bool) (x : ℝ × ℝ) : L1 η x = (x.1 + sgnB η * x.2, x.1 - sgnB η * x.2) := by
  simp [L1]; ring

/-- The chord through the points at angles `φ ± θ` (`η` picks the order). -/
lemma angles1_branch (b : ℝ) (hb : 0 < b) (η : Bool) {x : ℝ × ℝ} (hx : x ∈ sq) :
    angles1 b (proj (L1 η x)) = x ∧ pt 0 b (proj (L1 η x)).1 ≠ pt 0 b (proj (L1 η x)).2 := by
  obtain ⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩ := hx
  have hsφ : 0 < sin x.1 := sin_pos_of_pos_of_lt_pi h1 h2
  have hsθ : 0 < sin x.2 := sin_pos_of_pos_of_lt_pi h3 h4
  set l := 2 * b * sgnB η * sin x.2 with hl
  have hl0 : l ≠ 0 := by
    have : sgnB η ≠ 0 := by cases η <;> norm_num [sgnB]
    simp only [hl]; positivity
  have hd : pt 0 b (proj (L1 η x)).2 - pt 0 b (proj (L1 η x)).1 =
      (l * sin x.1, -(l * cos x.1)) := by
    simp only [proj, L1_apply, pt, ccos_coe, csin_coe, hl]
    cases η <;> simp [sgnB, cos_add, cos_sub, sin_add, sin_sub] <;> constructor <;> ring
  have hm : nrm (pt 0 b (proj (L1 η x)).1) (pt 0 b (proj (L1 η x)).2) = (cos x.1, sin x.1) := by
    rw [nrm, hd, nrmD_eq hl0 hsφ]
  refine ⟨?_, ?_⟩
  · unfold angles1
    rw [hm]
    have hB : (proj (L1 η x)).1 = ((x.1 + sgnB η * x.2 : ℝ) : Ang) := by simp [proj, L1_apply]
    rw [hB, off_pt 0 b x.1 _ hb.ne', show x.1 + sgnB η * x.2 - x.1 = sgnB η * x.2 by ring]
    have hc : cos (sgnB η * x.2) = cos x.2 := by cases η <;> simp [sgnB]
    rw [hc, arccos_cos h1.le h2.le, arccos_cos h3.le h4.le]
  · intro h
    have := hd
    rw [h, sub_self] at this
    have h0 := congrArg Prod.fst this
    simp only [Prod.fst_zero] at h0
    exact (mul_ne_zero hl0 hsφ.ne') h0.symm

/-- **Lemma 1.** The angle pair `(φ, θ_B)` of the chord `BC` is uniform on `(0, π)²`: its law under
`volume` on `Ang × Ang` (mass `4π²`) is `4 • volume` on the square (mass `4π²`). Moreover `B ≠ C`
almost surely. -/
theorem lemma1 (b : ℝ) (hb : 0 < b) :
    Measure.map (angles1 b) volume = (4 : ℝ≥0∞) • volume.restrict sq ∧
      ∀ᵐ ω ∂(volume : Measure (Ang × Ang)), pt 0 b ω.1 ≠ pt 0 b ω.2 := by
  have key := map_eq_of_branches (angles1 b) (measurable_angles1 b) sq measurableSet_sq 4
    (fun η => ⇑(L1 η)) (fun η _ => L1 η) (fun _ => sq) (fun _ => measurableSet_sq)
    (fun _ => subset_rfl) (fun η => if η then (0, -π) else (-π, 0))
    (by
      intro η x hx
      obtain ⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩ := hx
      simp only [L1_apply, box]
      cases η <;> simp [sgnB] <;> constructor <;> constructor <;> linarith)
    (fun η x _ => (L1 η).hasFDerivAt.hasFDerivWithinAt)
    (fun η x hx => (angles1_branch b hb η hx).1)
    (by
      intro i j hij x hx _ h
      obtain ⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩ := hx
      have hc := congrArg (fun ω : Ang × Ang => ccos ω.1) h
      simp only [proj, L1_apply, ccos_coe] at hc
      have hs := mul_pos (sin_pos_of_pos_of_lt_pi h1 h2) (sin_pos_of_pos_of_lt_pi h3 h4)
      cases i <;> cases j <;> simp_all [sgnB, cos_add] <;> linarith)
    (fun _ _ => 2) (fun _ => measurable_const)
    (by
      intro η x _
      rw [L1, det_two]
      cases η <;> norm_num [sgnB])
    (by intro η x hx; exact absurd hx.1 (fun h => hx.2 h))
    (by intro x _; simp; norm_num)
    four_mul_volume_sq
  refine ⟨key.1, ?_⟩
  filter_upwards [key.2] with ω hω
  obtain ⟨η, x, hx, rfl⟩ := hω
  exact (angles1_branch b hb η hx).2

end Chords
