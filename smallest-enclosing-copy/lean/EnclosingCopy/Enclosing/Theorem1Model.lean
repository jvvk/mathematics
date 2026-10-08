import EnclosingCopy.Enclosing.CertificateSharpness
import EnclosingCopy.Enclosing.FiniteCoercivity
import EnclosingCopy.Enclosing.TangentEventStability

/-!
# Theorem 1, the Poisson side: structure of every optimum

`general_classify` classifies optima that fit. The stability argument for Theorem 1 needs the
structure of every optimum, fitting or not:

* `optimum_structure`: an optimal copy of a finite configuration is the vertex copy of four
  points with a positive certificate, or the chord copy of a segment triple, or one of the null
  events `Opp2`, `Tri3`;
* `optimum_tilt_gap`: in the first two cases every feasible copy satisfies
  `|Θ - Θ*| ≤ D (ε - ε*)`, the hypothesis of `tangent_enclosing_event_stability`;
* `model_copy_bound`: shallow witnesses near both ends of every side put every feasible copy with
  `ε ≤ 0` in a fixed box (the limit-model analogue of `finite_tangent_copy_bound`).
-/

namespace Enclosing
open Set

variable {m : ℕ} (K : Sides m)

/-- **Every optimum is a certified vertex, a segment, or null.** -/
theorem optimum_structure (hG : GoodSides K) {n : ℕ} (y : Fin n → Pt m) (z : Copy)
    (hfeas : Feasible K (PoissonPP.config y) z)
    (hopt : ∀ z', Feasible K (PoissonPP.config y) z' → z.1 ≤ z'.1) :
    (∃ f : Fin 4 ↪ Fin n, (vertexMatrix K (y ∘ f)).det ≠ 0 ∧
        (∀ r, 0 < vertexCert K (y ∘ f) r) ∧ z = vertexCopy K (y ∘ f)) ∨
      (∃ k kb : Fin m, K.u kb = -K.u k ∧ ∃ g : Fin 3 ↪ Fin n, SegGood k kb (y ∘ g) ∧
        z = segCopy K k (segVec K k kb (y ∘ g)) (dot z.2.1 (tang K k))) ∨
      BadP (Opp2 K) ⟨n, y⟩ ∨ BadP (Tri3 K) ⟨n, y⟩ := by
  classical
  obtain ⟨t, μ, ht, hμ, hli, he⟩ := optimum_kkt K y z hfeas hopt
  have hle4 : t.card ≤ 4 := by
    have := hli.fintype_card_le_finrank
    simpa using this
  by_cases h4 : t.card = 4
  · left
    let e : t ≃ Fin 4 := t.equivFinOfCardEq h4
    let f : Fin 4 ↪ Fin n := ⟨fun r => (e.symm r).1, fun r r' hr =>
      e.symm.injective (Subtype.ext hr)⟩
    have hli4 : LinearIndependent ℝ (fun r => row K (y (f r))) :=
      hli.comp e.symm e.symm.injective
    have hA : (vertexMatrix K (y ∘ f)).det ≠ 0 := by
      have hu : IsUnit (vertexMatrix K (y ∘ f)) :=
        Matrix.linearIndependent_rows_iff_isUnit.mp hli4
      exact ((Matrix.isUnit_iff_isUnit_det _).mp hu).ne_zero
    have hsum : ∑ i ∈ t, μ i • row K (y i) = ∑ r, μ (f r) • row K (y (f r)) := by
      rw [← Finset.sum_coe_sort t]
      exact (Equiv.sum_comp e.symm (fun i : t => μ i • row K (y i))).symm
    have hcert : ∀ c, ∑ r, μ (f r) * row K ((y ∘ f) r) c = if c = 0 then 1 else 0 := by
      intro c
      have h1 := congrFun he c
      rw [hsum, Finset.sum_apply] at h1
      simp only [Pi.smul_apply, smul_eq_mul, Pi.single_apply] at h1
      exact h1.symm
    have hmem : ∀ r, f r ∈ t := fun r => (e.symm r).2
    have hc := vertexCert_eq_of_certificate K (y ∘ f) hA _ hcert
    have hz := vertexCopy_eq_of_tight K (y ∘ f) hA z fun r => ht _ (hmem r)
    refine ⟨f, hA, ?_, hz.symm⟩
    rw [hc]; exact fun r => hμ _ (hmem r)
  rcases general_support hG y t μ hμ hli he (by omega) with hS | hO | hT
  · right; left
    obtain ⟨k, kb, a, b, c, hu, htt, hab, hsa, hsb, hsc, h1, h2⟩ := hS
    have hP := hG.parPair hu
    have hac : a ≠ c := by intro h; rw [h, hsc] at hsa; exact hP.ne hsa.symm
    have hbc : b ≠ c := by intro h; rw [h, hsc] at hsb; exact hP.ne hsb.symm
    let g : Fin 3 ↪ Fin n := ⟨![a, b, c], fun r r' hr => by
      fin_cases r <;> fin_cases r' <;> simp_all [eq_comm]⟩
    have hg : SegGood k kb (y ∘ g) := ⟨hsa, hsb, hsc, h1, h2⟩
    have htight : ∀ r, gx K z ((y ∘ g) r) = 0 := by
      intro r
      fin_cases r
      · exact ht a (by rw [htt]; simp)
      · exact ht b (by rw [htt]; simp)
      · exact ht c (by rw [htt]; simp)
    exact ⟨k, kb, hu, g, hg, segCopy_of_tight K hP hg z htight⟩
  · right; right; left
    obtain ⟨a, -, b, -, hab, hO⟩ := hO
    exact badP_one y hab hO
  · right; right; right
    obtain ⟨a, -, b, -, c, -, hab, hac, hbc, hT⟩ := hT
    exact badP_two y hab hac hbc hT

/-- **Tilt gap at a non-null optimum.** -/
theorem optimum_tilt_gap (hG : GoodSides K) {n : ℕ} (y : Fin n → Pt m) (z : Copy)
    (hfeas : Feasible K (PoissonPP.config y) z)
    (hopt : ∀ z', Feasible K (PoissonPP.config y) z' → z.1 ≤ z'.1)
    (hO : ¬ BadP (Opp2 K) ⟨n, y⟩) (hT : ¬ BadP (Tri3 K) ⟨n, y⟩) :
    ∃ D ≥ 0, ∀ z', Feasible K (PoissonPP.config y) z' → |z'.2.2 - z.2.2| ≤ D * (z'.1 - z.1) := by
  rcases optimum_structure K hG y z hfeas hopt with ⟨f, hA, hc, rfl⟩ | ⟨k, kb, hu, g, hg, hz⟩ |
      h | h
  · obtain ⟨D, hD, hgap⟩ := vertex_tilt_gap K (y ∘ f) hA hc
    refine ⟨D, hD, fun z' hz' => (hgap z' fun r => ?_).2⟩
    exact (feasible_config_iff K y z').mp hz' (f r)
  · have hP := hG.parPair hu
    obtain ⟨D, hD, hgap⟩ := segment_tilt_gap hP hg (dot z.2.1 (tang K k))
    refine ⟨D, hD, fun z' hz' => ?_⟩
    have h := (hgap z' fun r => (feasible_config_iff K y z').mp hz' (g r)).2
    have h1 : z.1 = segVec K k kb (y ∘ g) 0 := by rw [hz]; rfl
    rw [h1]; rw [← hz] at h; exact h
  · exact absurd h hO
  · exact absurd h hT

variable [NeZero m]

/-- **Coercivity in the limit model**: shallow witnesses near both ends of every side put every
feasible copy with `ε ≤ 0` in a fixed box. -/
theorem model_copy_bound (hG : GoodSides K) {M : ℝ} (hM : 0 ≤ M) :
    ∃ ρ ≥ 0, ∀ wp wm : Fin m → Pt m, Wit K wp wm →
      (∀ i, (wp i).2.2 ≤ M) → (∀ i, (wm i).2.2 ≤ M) → ∀ z : Copy, z.1 ≤ 0 →
      (∀ i, ¬ violates K z (wp i)) → (∀ i, ¬ violates K z (wm i)) →
      |z.1| ≤ ρ ∧ |z.2.1.1| ≤ ρ ∧ |z.2.1.2| ≤ ρ ∧ |z.2.2| ≤ ρ := by
  let B := 4 * M * per K / Qs K
  have hQ := Qs_pos K
  have hper := per_pos K
  have hB : 0 ≤ B := by dsimp [B]; positivity
  let E := (B * Sb K + M) * per K / 2
  have hSb : 0 ≤ Sb K := Finset.sum_nonneg fun i _ => by positivity
  have hE : 0 ≤ E := by dsimp [E]; positivity
  let H := ∑ i, |K.h i|
  have hH : 0 ≤ H := Finset.sum_nonneg fun _ _ => abs_nonneg _
  let A := B * Sb K + M + E * H
  have hA : 0 ≤ A := by dsimp [A]; positivity
  obtain ⟨j, hj⟩ := hG.nondeg (0 : Fin m)
  let U := A + A * per K / Ls K 0
  let V := A + A * per K / Ls K j
  have hU : 0 ≤ U := by dsimp [U]; positivity [Ls_pos K 0]
  have hV : 0 ≤ V := by dsimp [V]; positivity [Ls_pos K j]
  let C := (U * (|(K.u j).1| + |(K.u j).2|) +
    V * (|(K.u 0).1| + |(K.u 0).2|)) /
      |(K.u 0).1 * (K.u j).2 - (K.u 0).2 * (K.u j).1|
  have hC : 0 ≤ C := by dsimp [C]; positivity
  refine ⟨B + E + C, by positivity, ?_⟩
  intro wp wm hW hDp hDm z hz hp hm
  have ht : |z.2.2| ≤ B := by
    have h := tilt_bound K wp wm hW.ps hW.ms hW.pp hW.mm hW.pD hW.mD z hz hp hm
    refine h.trans ?_
    dsimp [B]
    apply div_le_div_of_nonneg_right _ hQ.le
    have hs : ∑ i, Ls K i * ((wp i).2.2 + (wm i).2.2) ≤ ∑ i, Ls K i * (2 * M) :=
      Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left
        (by linarith [hDp i, hDm i]) (Ls_pos K i).le
    have he : ∑ i, Ls K i * (2 * M) = 2 * M * per K := by
      rw [per, Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by ring
    linarith
  have hpos (i : Fin m) : |(wp i).2.1| ≤ Sb K :=
    (abs_le_of_mem_Icc (hW.pI i)).trans (single_le_Sb K i)
  have hg (i : Fin m) : -(B * Sb K + M) ≤ Hs K z i := by
    have h := Hs_ge_of_not_violates K (hp i)
    rw [hW.ps i] at h
    have htprod : |z.2.2 * (wp i).2.1| ≤ B * Sb K := by
      rw [abs_mul]; exact mul_le_mul ht (hpos i) (abs_nonneg _) hB
    linarith [neg_abs_le (z.2.2 * (wp i).2.1), hDp i]
  have hsum := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) =>
    mul_le_mul_of_nonneg_left (hg i) (Ls_pos K i).le)
  rw [sum_Ls_Hs] at hsum
  have hsumleft : ∑ i, Ls K i * -(B * Sb K + M) = -(B * Sb K + M) * per K := by
    simp only [per, Finset.mul_sum]; apply Finset.sum_congr rfl; intro i _; ring
  rw [hsumleft] at hsum
  have he : |z.1| ≤ E := by
    rw [abs_le]; dsimp [E]; constructor <;> nlinarith
  have hnormal (i : Fin m) : -A ≤ dot z.2.1 (K.u i) := by
    have hhi : |K.h i| ≤ H := Finset.single_le_sum
      (f := fun j => |K.h j|) (fun _ _ => abs_nonneg _) (Finset.mem_univ i)
    have hmul : |z.1 * K.h i| ≤ E * H := by
      rw [abs_mul]; exact mul_le_mul he hhi (abs_nonneg _) hE
    have hh := hg i
    unfold Hs at hh
    dsimp [A]
    linarith [le_abs_self (z.1 * K.h i)]
  have hc := coords_bounded (K.u 0) (K.u j) z.2.1 hj U V
    (balanced_normal_abs_bound K z.2.1 hA hnormal 0)
    (balanced_normal_abs_bound K z.2.1 hA hnormal j)
  exact ⟨by linarith, by linarith [hc.1], by linarith [hc.2], by linarith⟩

end Enclosing
