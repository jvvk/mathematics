import EnclosingCopy.Enclosing.Theorem1Step0
import EnclosingCopy.Enclosing.TangentFit

/-!
# Theorem 1: the physical event and the windowed finite event

`TrueEv K x` is the event of the question: some smallest similar copy of the polygon
containing the sample points lies in the polygon. On the good event (sample in the polygon, no
point in a corner overlap, witnesses near both ends of every side, the sample covering the
polygon to within `δ`), and for large `n`, it is exactly the windowed finite event
`EvN K R M n` of the boundary marks (`trueEv_iff_evN`).

The steps: every similarity with rotation below `π/2` is a tangent copy (`tangent_param`);
Step 0 puts the rotation of every copy of scale at most one near a symmetry, which can be
removed (`small_angle_rep`); witnesses then bound the copy (Codex's `finite_tangent_copy_bound`);
in the box, containment is feasibility for the boundary marks and fitting is `TangentFits`.
-/

namespace Enclosing
open MeasureTheory Set Filter Topology Real Metric

variable {m : ℕ} [NeZero m] (K : Sides m)

/-- The boundary marks of a sample. -/
noncomputable def winMarks (T : ℝ) (n : ℕ) {k : ℕ} (x : Fin k → ℝ × ℝ) : Multiset (Pt m) :=
  (PoissonPP.inWindow (physicalBoundaryWindow K T n) (PoissonPP.config x)).map
    (physicalBoundaryMark K T n)

/-- **The event of the question**: some smallest copy containing the sample lies in the
polygon. -/
def TrueEv {k : ℕ} (x : Fin k → ℝ × ℝ) : Prop :=
  ∃ l θ c, 0 < l ∧ (∀ j, x j ∈ simCopy K l θ c) ∧
    (∀ l' θ' c', 0 < l' → (∀ j, x j ∈ simCopy K l' θ' c') → l ≤ l') ∧
    simCopy K l θ c ⊆ polygonRegion K

lemma tangentCopyRegion_eq_simCopy (q : ℝ) (z : Copy) :
    tangentCopyRegion K q z =
      simCopy K (tangentScale q z) (arctan (q * z.2.2)) (tangentShift q z) := by
  ext x
  simp only [tangentCopyRegion, simCopy, simMap, mem_image, tangentSimilarity_is_similarity]

lemma simCopy_one_zero : simCopy K 1 0 0 = polygonRegion K := by
  ext x; simp [simCopy, simMap, planeRotate]

lemma tangentScale_zero (q : ℝ) : tangentScale q zeroCopy = 1 := by
  simp [tangentScale, zeroCopy]

lemma tangentCopyRegion_zero (q : ℝ) : tangentCopyRegion K q zeroCopy = polygonRegion K := by
  ext x
  simp [tangentCopyRegion, tangentSimilarity, zeroCopy, tangentRotate]

/-- **Every similarity with rotation below `π/2` is a tangent copy.** -/
lemma tangent_param {q : ℝ} (hq : 0 < q) {l : ℝ} (hl : 0 < l) {θ : ℝ} (hθ : |θ| < π / 2)
    (c : ℝ × ℝ) :
    ∃ z : Copy, 0 < 1 + q * z.1 ∧ tangentScale q z = l ∧ q * z.2.2 = tan θ ∧
      tangentCopyRegion K q z = simCopy K l θ c := by
  set t := tan θ
  have hs : 0 < sqrt (1 + t ^ 2) := sqrt_pos.2 (by positivity)
  set z : Copy := ((l * sqrt (1 + t ^ 2) - 1) / q, (1 / q) • tangentRotate (-t) c, t / q)
  have h1 : 1 + q * z.1 = l * sqrt (1 + t ^ 2) := by
    simp only [z]; field_simp; ring
  have h3 : q * z.2.2 = t := by simp only [z]; field_simp
  have hscale : tangentScale q z = l := by
    unfold tangentScale; rw [h1, h3]; field_simp
  have hangle : arctan (q * z.2.2) = θ := by
    rw [h3]; exact arctan_tan (by linarith [neg_abs_le θ]) (by linarith [le_abs_self θ])
  have hshift : tangentShift q z = c := by
    unfold tangentShift
    rw [h3]
    have hz2 : q • z.2.1 = tangentRotate (-t) c := by
      simp only [z, smul_smul]; field_simp; exact one_smul _ _
    rw [hz2]
    have := tangentRotate_neg (-t) c
    rw [neg_neg] at this
    rw [this, smul_smul]
    have hd : 1 + (-t) ^ 2 ≠ 0 := by positivity
    rw [show (1 / (1 + t ^ 2)) * (1 + (-t) ^ 2) = 1 by field_simp, one_smul]
  refine ⟨z, by rw [h1]; positivity, hscale, h3, ?_⟩
  rw [tangentCopyRegion_eq_simCopy, hscale, hangle, hshift]

lemma abs_tan_le {a η : ℝ} (ha : |a| < η) (hη : η < π / 2) : |tan a| ≤ tan η := by
  have hη0 : 0 ≤ η := le_trans (abs_nonneg a) ha.le
  have hmono : tan |a| ≤ tan η :=
    (Real.strictMonoOn_tan.monotoneOn) ⟨by linarith [abs_nonneg a, pi_pos], by linarith⟩
      ⟨by linarith [pi_pos], hη⟩ ha.le
  have hle : a ≤ π / 2 := by linarith [le_abs_self a]
  have hle' : -a ≤ π / 2 := by linarith [neg_abs_le a]
  have key : |tan a| = tan |a| := by
    rcases le_total 0 a with h | h
    · rw [abs_of_nonneg h, abs_of_nonneg (tan_nonneg_of_nonneg_of_le_pi_div_two h hle)]
    · have ht := tan_nonneg_of_nonneg_of_le_pi_div_two (neg_nonneg.mpr h) hle'
      rw [tan_neg] at ht
      rw [abs_of_nonpos h, tan_neg, abs_of_nonpos (by linarith)]
  rw [key]; exact hmono

/-- Points of the boundary marks come from sample points in side strips. -/
lemma mem_winMarks {T : ℝ} {n k : ℕ} {x : Fin k → ℝ × ℝ} {p : Pt m}
    (hp : p ∈ winMarks K T n x) :
    ∃ j i, x j ∈ physicalSideStrip K i (T / n) ∧ p = physicalBoundaryMark K T n (x j) := by
  obtain ⟨y, hy, rfl⟩ := Multiset.mem_map.mp hp
  have hy' : y ∈ PoissonPP.config x ∧ y ∈ physicalBoundaryWindow K T n := by
    simpa only [PoissonPP.inWindow, Multiset.mem_filter] using hy
  obtain ⟨j, rfl⟩ := (PoissonPP.mem_config x y).mp hy'.1
  obtain ⟨i, hi⟩ := mem_iUnion.mp hy'.2
  exact ⟨j, i, hi, rfl⟩

/-- Containment of the sample in a tangent copy makes it feasible for the boundary marks; no
box is needed in this direction. -/
lemma containment_feasible {T : ℝ} {n k : ℕ} (hn : 0 < n) {x : Fin k → ℝ × ℝ}
    (hcorner : ∀ j, x j ∉ cornerOverlap K (T / n)) {z : Copy}
    (hz : 0 < 1 + (1 / (n : ℝ)) * z.1) (hc : ∀ j, x j ∈ tangentCopyRegion K (1 / n) z) :
    Feasible K (winMarks K T n x) z := by
  have hq : 0 < (1 : ℝ) / n := one_div_pos.mpr (by exact_mod_cast hn)
  intro p hp
  obtain ⟨j, i, hi, rfl⟩ := mem_winMarks K hp
  rw [physicalBoundaryMark_eq_tangentPointMark K hn hi (hcorner j)]
  exact (mem_tangentCopyRegion_iff_model K hq hz (x j)).mp (hc j) i

/-- **Small-angle representative**: on a `δ`-cover, a copy of scale at most one containing the
sample is a tangent copy with `|q Θ| ≤ tan η`. -/
lemma small_angle_rep {δ η : ℝ} (hηπ : η < π / 2)
    (hstep0 : ∀ S : Set (ℝ × ℝ), (polygonRegion K ⊆ ⋃ s ∈ S, closedBall s δ) →
      ∀ l θ c, 0 < l → l ≤ 1 → S ⊆ simCopy K l θ c → ∃ θ₀, SymAngle K θ₀ ∧ |θ - θ₀| < η)
    {q : ℝ} (hq : 0 < q) {k : ℕ} {x : Fin k → ℝ × ℝ}
    (hnet : polygonRegion K ⊆ ⋃ s ∈ range x, closedBall s δ)
    {l θ : ℝ} {c : ℝ × ℝ} (hl : 0 < l) (hl1 : l ≤ 1) (hc : ∀ j, x j ∈ simCopy K l θ c) :
    ∃ z : Copy, 0 < 1 + q * z.1 ∧ tangentScale q z = l ∧ |q * z.2.2| ≤ tan η ∧
      tangentCopyRegion K q z = simCopy K l θ c := by
  obtain ⟨θ₀, hsym, hclose⟩ := hstep0 (range x) hnet l θ c hl hl1 (range_subset_iff.2 hc)
  obtain ⟨c', heq⟩ := simCopy_symm K hsym l θ c
  obtain ⟨z, hz1, hzs, hzt, hzr⟩ :=
    tangent_param K hq hl (show |θ - θ₀| < π / 2 by linarith) c'
  exact ⟨z, hz1, hzs, by rw [hzt]; exact abs_tan_le hclose hηπ, by rw [hzr, heq]⟩

/-- **On the good event the event of the question is the windowed finite event.** -/
theorem trueEv_iff_evN {M R T η δ r : ℝ} {n : ℕ} (hn : 0 < n)
    (hqR : (1 / (n : ℝ)) * R < 1) (hrR : (1 / (n : ℝ)) * R ≤ r)
    (hηπ : η < π / 2) (htanr : tan η ≤ r) (htanQ : tan η ≤ Qs K / 4)
    (hfit : ∀ q > 0, ∀ z : Copy, 0 < 1 + q * z.1 → |q * z.2.2| ≤ r →
      (tangentCopyRegion K q z ⊆ polygonRegion K ↔ TangentFits K q z))
    (hboxF : ∀ wp wm : Fin m → Pt m, Wit K wp wm → (∀ i, (wp i).2.2 ≤ M) →
      (∀ i, (wm i).2.2 ≤ M) → ∀ q : ℝ, 0 < q → q ≤ 1 → ∀ z : Copy,
        tangentScale q z ≤ 1 → |q * z.2.2| ≤ Qs K / 4 →
        (∀ i, ¬ violates K z (wp i)) → (∀ i, ¬ violates K z (wm i)) → z ∈ copyBox R)
    (hline : ∀ y ∈ polygonRegion K, ∀ z ∈ copyBox R, ∀ i,
      z.2.2 * dot y (sideTangent (K.u i)) - Hs K z i ≤ T)
    (hstep0 : ∀ S : Set (ℝ × ℝ), (polygonRegion K ⊆ ⋃ s ∈ S, closedBall s δ) →
      ∀ l θ c, 0 < l → l ≤ 1 → S ⊆ simCopy K l θ c → ∃ θ₀, SymAngle K θ₀ ∧ |θ - θ₀| < η)
    {x : Fin n → ℝ × ℝ} (hx : ∀ j, x j ∈ polygonRegion K)
    (hcorner : ∀ j, x j ∉ cornerOverlap K (T / n))
    (hwit : WitEv K M (winMarks K T n x))
    (hnet : polygonRegion K ⊆ ⋃ s ∈ range x, closedBall s δ) :
    TrueEv K x ↔ EvN K R M n (winMarks K T n x) := by
  set q : ℝ := 1 / (n : ℝ)
  have hq : 0 < q := one_div_pos.mpr (by exact_mod_cast hn)
  have hq1 : q ≤ 1 := by
    simp only [q]; rw [div_le_one (by exact_mod_cast hn)]; exact_mod_cast hn
  obtain ⟨wp, wm, hW, hmem, hdM⟩ := witEv_wit K hwit
  -- a feasible tangent copy of scale at most one and small tilt lies in the box
  have hinbox : ∀ z : Copy, 0 < 1 + q * z.1 → tangentScale q z ≤ 1 → |q * z.2.2| ≤ tan η →
      (∀ j, x j ∈ tangentCopyRegion K q z) → z ∈ copyBox R := by
    intro z hz hs ht hc
    have hf := containment_feasible K hn hcorner hz hc
    exact hboxF wp wm hW (fun i => (hdM i).1) (fun i => (hdM i).2) q hq hq1 z hs
      (ht.trans htanQ) (fun i => hf _ (hmem i).1) (fun i => hf _ (hmem i).2)
  have hboxpos : ∀ z ∈ copyBox R, 0 < 1 + q * z.1 := by
    intro z hz
    have h1 : |q * z.1| ≤ q * R := by
      rw [abs_mul, abs_of_pos hq]; exact mul_le_mul_of_nonneg_left hz.1 hq.le
    linarith [neg_abs_le (q * z.1)]
  have hboxtilt : ∀ z ∈ copyBox R, |q * z.2.2| ≤ r := by
    intro z hz
    rw [abs_mul, abs_of_pos hq]
    exact (mul_le_mul_of_nonneg_left hz.2.2.2 hq.le).trans hrR
  -- in the box, feasibility gives containment
  have hcont : ∀ z ∈ copyBox R, Feasible K (winMarks K T n x) z →
      ∀ j, x j ∈ tangentCopyRegion K q z := fun z hz hf =>
    (sample_containment_iff_boundary_feasible K hn x hx hcorner z (hboxpos z hz)
      (fun j i => hline (x j) (hx j) z hz i)).2 hf
  have hP : ∀ j, x j ∈ simCopy K 1 0 0 := fun j => by rw [simCopy_one_zero]; exact hx j
  constructor
  · rintro ⟨l, θ, c, hl, hc, hmin, hfitP⟩
    have hl1 : l ≤ 1 := hmin 1 0 0 one_pos hP
    obtain ⟨z, hz1, hzs, hzt, hzr⟩ := small_angle_rep K hηπ hstep0 hq hnet hl hl1 hc
    have hcz : ∀ j, x j ∈ tangentCopyRegion K q z := fun j => by rw [hzr]; exact hc j
    have hzb := hinbox z hz1 (by rw [hzs]; exact hl1) hzt hcz
    refine ⟨hwit, z, hzb, containment_feasible K hn hcorner hz1 hcz,
      (hfit q hq z hz1 (hzt.trans htanr)).1 (by rw [hzr]; exact hfitP), fun y hyb hyf => ?_⟩
    have hcy := hcont y hyb hyf
    rw [hzs]
    have hyp := hboxpos y hyb
    apply hmin _ _ _ (tangentScale_pos hyp)
    intro j
    have := hcy j
    rwa [tangentCopyRegion_eq_simCopy] at this
  · rintro ⟨-, z, hzb, hzf, hzt, hzm⟩
    have hz1 := hboxpos z hzb
    have hcz := hcont z hzb hzf
    refine ⟨tangentScale q z, arctan (q * z.2.2), tangentShift q z, tangentScale_pos hz1,
      fun j => by rw [← tangentCopyRegion_eq_simCopy]; exact hcz j, ?_,
      by rw [← tangentCopyRegion_eq_simCopy]; exact (hfit q hq z hz1 (hboxtilt z hzb)).2 hzt⟩
    intro l' θ' c' hl' hc'
    by_contra hlt
    push Not at hlt
    -- the zero copy is feasible, so the optimum has scale at most one
    have h0b : zeroCopy ∈ copyBox R := by
      have : 0 ≤ R := le_trans (abs_nonneg _) hzb.1
      simp [copyBox, zeroCopy, this]
    have h0f : Feasible K (winMarks K T n x) zeroCopy :=
      containment_feasible K hn hcorner (by simp [zeroCopy])
        (fun j => by rw [tangentCopyRegion_zero]; exact hx j)
    have hz1le : tangentScale q z ≤ 1 := by
      have := hzm zeroCopy h0b h0f; rwa [tangentScale_zero] at this
    obtain ⟨z', hz'1, hz's, hz't, hz'r⟩ :=
      small_angle_rep K hηπ hstep0 hq hnet hl' (by linarith) hc'
    have hcz' : ∀ j, x j ∈ tangentCopyRegion K q z' := fun j => by rw [hz'r]; exact hc' j
    have hz'b := hinbox z' hz'1 (by rw [hz's]; linarith) hz't hcz'
    have := hzm z' hz'b (containment_feasible K hn hcorner hz'1 hcz')
    rw [hz's] at this
    linarith

end Enclosing
