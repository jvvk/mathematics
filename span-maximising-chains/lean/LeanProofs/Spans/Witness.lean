import LeanProofs.Spans.N4
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.Real.Pi.Bounds

/-!
# Span-maximizing chains: each four-segment pattern occurs (`a₄ = 3`)

A turn `A = 2 arctan x` has `e^{iA} = ((1 - x²) + 2x i)/(1 + x²)`, so spans of data with rational half-angle
tangents are exact rationals. For sorted data, the maximum over all rearrangements is attained by an optimum,
which by `n4_classify` (applied to it or to its reversal) has one of the three patterns. So if the target
pattern's span is at least the other two patterns' spans, the target arrangement is optimal.
-/

open Complex Finset Real

namespace Spans

lemma e_two_arctan (x : ℝ) : e (2 * arctan x) = ⟨(1 - x ^ 2) / (1 + x ^ 2), 2 * x / (1 + x ^ 2)⟩ := by
  have hs : (0 : ℝ) < 1 + x ^ 2 := by positivity
  have hsq : √(1 + x ^ 2) ^ 2 = 1 + x ^ 2 := Real.sq_sqrt hs.le
  have hsq0 : 0 < √(1 + x ^ 2) := Real.sqrt_pos.2 hs
  apply Complex.ext
  · rw [e_re, Real.cos_two_mul, cos_arctan]
    field_simp
    rw [hsq]; ring
  · rw [e_im, Real.sin_two_mul, sin_arctan, cos_arctan]
    field_simp
    rw [hsq]

/-! ## Forcing a rearrangement of sorted data from its order pattern -/

section forcing
variable {Ls : Fin 4 → ℝ} {As : Fin 3 → ℝ}

lemma force_L1 (hL : StrictMono Ls) (σ : Equiv.Perm (Fin 4))
    (h : Ls (σ 0) < Ls (σ 3) ∧ Ls (σ 3) < Ls (σ 1) ∧ Ls (σ 1) < Ls (σ 2)) :
    Ls ∘ σ = ![Ls 0, Ls 2, Ls 3, Ls 1] := by
  obtain ⟨h1, h2, h3⟩ := h
  rw [hL.lt_iff_lt] at h1 h2 h3
  rw [Fin.lt_def] at h1 h2 h3
  have b0 := (σ 0).isLt; have b1 := (σ 1).isLt; have b2 := (σ 2).isLt; have b3 := (σ 3).isLt
  have e0 : σ 0 = 0 := Fin.ext (by simp; omega)
  have e1 : σ 1 = 2 := Fin.ext (by simp; omega)
  have e2 : σ 2 = 3 := Fin.ext (by simp; omega)
  have e3 : σ 3 = 1 := Fin.ext (by simp; omega)
  funext i; fin_cases i <;> simp [e0, e1, e2, e3]

lemma force_L2 (hL : StrictMono Ls) (σ : Equiv.Perm (Fin 4))
    (h : Ls (σ 0) < Ls (σ 3) ∧ Ls (σ 3) < Ls (σ 2) ∧ Ls (σ 2) < Ls (σ 1)) :
    Ls ∘ σ = ![Ls 0, Ls 3, Ls 2, Ls 1] := by
  obtain ⟨h1, h2, h3⟩ := h
  rw [hL.lt_iff_lt] at h1 h2 h3
  rw [Fin.lt_def] at h1 h2 h3
  have b0 := (σ 0).isLt; have b1 := (σ 1).isLt; have b2 := (σ 2).isLt; have b3 := (σ 3).isLt
  have e0 : σ 0 = 0 := Fin.ext (by simp; omega)
  have e1 : σ 1 = 3 := Fin.ext (by simp; omega)
  have e2 : σ 2 = 2 := Fin.ext (by simp; omega)
  have e3 : σ 3 = 1 := Fin.ext (by simp; omega)
  funext i; fin_cases i <;> simp [e0, e1, e2, e3]

lemma force_A1 (hA : StrictMono As) (τ : Equiv.Perm (Fin 3)) (h : As (τ 1) < As (τ 2) ∧ As (τ 2) < As (τ 0)) :
    As ∘ τ = ![As 2, As 0, As 1] := by
  obtain ⟨h1, h2⟩ := h
  rw [hA.lt_iff_lt, Fin.lt_def] at h1 h2
  have b0 := (τ 0).isLt; have b1 := (τ 1).isLt; have b2 := (τ 2).isLt
  have e0 : τ 0 = 2 := Fin.ext (by simp; omega)
  have e1 : τ 1 = 0 := Fin.ext (by simp; omega)
  have e2 : τ 2 = 1 := Fin.ext (by simp; omega)
  funext i; fin_cases i <;> simp [e0, e1, e2]

lemma force_A3 (hA : StrictMono As) (τ : Equiv.Perm (Fin 3)) (h : As (τ 1) < As (τ 0) ∧ As (τ 0) < As (τ 2)) :
    As ∘ τ = ![As 1, As 0, As 2] := by
  obtain ⟨h1, h2⟩ := h
  rw [hA.lt_iff_lt, Fin.lt_def] at h1 h2
  have b0 := (τ 0).isLt; have b1 := (τ 1).isLt; have b2 := (τ 2).isLt
  have e0 : τ 0 = 1 := Fin.ext (by simp; omega)
  have e1 : τ 1 = 0 := Fin.ext (by simp; omega)
  have e2 : τ 2 = 2 := Fin.ext (by simp; omega)
  funext i; fin_cases i <;> simp [e0, e1, e2]

end forcing

/-! ## Optimality from the three pattern values -/

section generic
variable {Ls : Fin 4 → ℝ} {As : Fin 3 → ℝ}

lemma admissible_sorted (hL : StrictMono Ls) (hA : StrictMono As) (hL0 : 0 < Ls 0) (hA0 : 0 < As 0)
    (hT : As 0 + As 1 + As 2 < π) (σ : Equiv.Perm (Fin 4)) (τ : Equiv.Perm (Fin 3)) :
    Admissible (Ls ∘ σ) (As ∘ τ) where
  lpos i := lt_of_lt_of_le hL0 (hL.monotone (Fin.zero_le _))
  linj := hL.injective.comp σ.injective
  apos j := lt_of_lt_of_le hA0 (hA.monotone (Fin.zero_le _))
  ainj := hA.injective.comp τ.injective
  Tlt := by
    unfold T
    obtain ⟨-, -, t3⟩ := θ3 (As ∘ τ)
    rw [t3]
    have := Equiv.sum_comp τ As
    simp only [Fin.sum_univ_three, Function.comp_apply] at this ⊢
    linarith

/-- If the target arrangement's span is at least the span of each of the three patterns, it is optimal. -/
theorem n4_optimal_of_values (hL : StrictMono Ls) (hA : StrictMono As) (hL0 : 0 < Ls 0) (hA0 : 0 < As 0)
    (hT : As 0 + As 1 + As 2 < π) (σ0 : Equiv.Perm (Fin 4)) (τ0 : Equiv.Perm (Fin 3))
    (h1 : ‖Z ![Ls 0, Ls 2, Ls 3, Ls 1] ![As 2, As 0, As 1]‖ ≤ ‖Z (Ls ∘ σ0) (As ∘ τ0)‖)
    (h2 : ‖Z ![Ls 0, Ls 3, Ls 2, Ls 1] ![As 2, As 0, As 1]‖ ≤ ‖Z (Ls ∘ σ0) (As ∘ τ0)‖)
    (h3 : ‖Z ![Ls 0, Ls 2, Ls 3, Ls 1] ![As 1, As 0, As 2]‖ ≤ ‖Z (Ls ∘ σ0) (As ∘ τ0)‖) :
    Optimal (Ls ∘ σ0) (As ∘ τ0) := by
  set target := ‖Z (Ls ∘ σ0) (As ∘ τ0)‖
  let g : Equiv.Perm (Fin 4) × Equiv.Perm (Fin 3) → ℝ := fun p => ‖Z (Ls ∘ p.1) (As ∘ p.2)‖
  obtain ⟨⟨σs, τs⟩, -, hmax⟩ := exists_max_image univ g univ_nonempty
  have hg : ∀ σ τ, g (σ, τ) ≤ g (σs, τs) := fun σ τ => hmax _ (mem_univ _)
  -- every optimum of sorted data whose shortest segment is first has a pattern value at most `target`
  have classify : ∀ (σ' : Equiv.Perm (Fin 4)) (τ' : Equiv.Perm (Fin 3)), Optimal (Ls ∘ σ') (As ∘ τ') → (∀ j, j ≠ 0 → (Ls ∘ σ') 0 < (Ls ∘ σ') j) →
      ‖Z (Ls ∘ σ') (As ∘ τ')‖ ≤ target := by
    intro σ' τ' ho hmin
    rcases n4_classify (admissible_sorted hL hA hL0 hA0 hT σ' τ') ho hmin with p | p | p
    · rw [force_L1 hL σ' ⟨p.1, p.2.1, p.2.2.1⟩, force_A1 hA τ' ⟨p.2.2.2.1, p.2.2.2.2⟩]; exact h1
    · rw [force_L2 hL σ' ⟨p.1, p.2.1, p.2.2.1⟩, force_A1 hA τ' ⟨p.2.2.2.1, p.2.2.2.2⟩]; exact h2
    · rw [force_L1 hL σ' ⟨p.1, p.2.1, p.2.2.1⟩, force_A3 hA τ' ⟨p.2.2.2.1, p.2.2.2.2⟩]; exact h3
  have optOf : ∀ (σ' : Equiv.Perm (Fin 4)) (τ' : Equiv.Perm (Fin 3)), g (σ', τ') = g (σs, τs) → Optimal (Ls ∘ σ') (As ∘ τ') := by
    intro σ' τ' he σ τ
    calc ‖Z ((Ls ∘ σ') ∘ σ) ((As ∘ τ') ∘ τ)‖ = g (σ.trans σ', τ.trans τ') := rfl
      _ ≤ g (σs, τs) := hg _ _
      _ = ‖Z (Ls ∘ σ') (As ∘ τ')‖ := he.symm
  have key : g (σs, τs) ≤ target := by
    have hadm := admissible_sorted hL hA hL0 hA0 hT σs τs
    have hopt := optOf σs τs rfl
    obtain ⟨s, -, hs⟩ := exists_min_image univ (Ls ∘ σs) univ_nonempty
    have hs' : ∀ j, j ≠ s → (Ls ∘ σs) s < (Ls ∘ σs) j := fun j hj =>
      lt_of_le_of_ne (hs j (mem_univ _)) (fun he => hj (hadm.linj he).symm)
    rcases shortest_at_end hadm hopt (by norm_num) hs' with h0 | h3'
    · have : s = 0 := Fin.ext h0
      subst this
      exact classify σs τs hopt hs'
    · have : s = 3 := Fin.ext h3'
      subst this
      have hrev : g (Fin.revPerm.trans σs, Fin.revPerm.trans τs) = g (σs, τs) := by
        show ‖Z ((Ls ∘ σs) ∘ Fin.revPerm) ((As ∘ τs) ∘ Fin.revPerm)‖ = ‖Z (Ls ∘ σs) (As ∘ τs)‖
        exact norm_Z_rev _ _
      have hmin : ∀ j : Fin 4, j ≠ 0 →
          (Ls ∘ (Fin.revPerm.trans σs)) 0 < (Ls ∘ (Fin.revPerm.trans σs)) j := fun j hj => by
        show (Ls ∘ σs) (Fin.rev 0) < (Ls ∘ σs) (Fin.rev j)
        have r0 : Fin.rev (0 : Fin 4) = 3 := rfl
        rw [r0]
        exact hs' _ (fun hc => hj (by rw [← Fin.rev_rev j, hc]; rfl))
      have := classify _ _ (optOf _ _ hrev) hmin
      calc g (σs, τs) = g (Fin.revPerm.trans σs, Fin.revPerm.trans τs) := hrev.symm
        _ ≤ target := this
  intro σ τ
  calc ‖Z ((Ls ∘ σ0) ∘ σ) ((As ∘ τ0) ∘ τ)‖ = g (σ.trans σ0, τ.trans τ0) := rfl
    _ ≤ g (σs, τs) := hg _ _
    _ ≤ target := key

end generic

/-! ## The three witnesses -/

lemma norm_le_of_normSq {z w : ℂ} (h : Complex.normSq z ≤ Complex.normSq w) : ‖z‖ ≤ ‖w‖ := by
  rw [Complex.norm_def, Complex.norm_def]; exact Real.sqrt_le_sqrt h

def Ls1 : Fin 4 → ℝ := ![1, 2, 3, 4]
noncomputable def As1 : Fin 3 → ℝ := ![2 * arctan (1 / 10), 2 * arctan (2 / 10), 2 * arctan (3 / 10)]
lemma e_As1_0 : e (As1 0) = ⟨99 / 101, 20 / 101⟩ := by
  rw [show As1 0 = 2 * arctan (1 / 10) from rfl, e_two_arctan]; norm_num
lemma e_As1_1 : e (As1 1) = ⟨12 / 13, 5 / 13⟩ := by
  rw [show As1 1 = 2 * arctan (2 / 10) from rfl, e_two_arctan]; norm_num
lemma e_As1_2 : e (As1 2) = ⟨91 / 109, 60 / 109⟩ := by
  rw [show As1 2 = 2 * arctan (3 / 10) from rfl, e_two_arctan]; norm_num
lemma val_1_P1 : Complex.normSq (Z ![Ls1 0, Ls1 2, Ls1 3, Ls1 1] ![As1 2, As1 0, As1 1]) = 12945800 / 143117 := by
  rw [Z4]; simp [Ls1, Complex.normSq_apply, Complex.mul_re, Complex.mul_im, e_As1_0, e_As1_1, e_As1_2]; norm_num
lemma val_1_P2 : Complex.normSq (Z ![Ls1 0, Ls1 3, Ls1 2, Ls1 1] ![As1 2, As1 0, As1 1]) = 994436 / 11009 := by
  rw [Z4]; simp [Ls1, Complex.normSq_apply, Complex.mul_re, Complex.mul_im, e_As1_0, e_As1_1, e_As1_2]; norm_num
lemma val_1_P3 : Complex.normSq (Z ![Ls1 0, Ls1 2, Ls1 3, Ls1 1] ![As1 1, As1 0, As1 2]) = 126250 / 1417 := by
  rw [Z4]; simp [Ls1, Complex.normSq_apply, Complex.mul_re, Complex.mul_im, e_As1_0, e_As1_1, e_As1_2]; norm_num
lemma mono_Ls1 : StrictMono Ls1 := by
  refine Fin.strictMono_iff_lt_succ.2 fun i => ?_; fin_cases i <;> norm_num [Ls1]
lemma mono_As1 : StrictMono As1 := by
  refine Fin.strictMono_iff_lt_succ.2 fun i => ?_
  fin_cases i <;> norm_num [As1, arctan_lt_arctan_iff]
lemma pos_As1 : 0 < As1 0 := by simp [As1, arctan_pos]
lemma sum_As1 : As1 0 + As1 1 + As1 2 ≤ π / 2 := by
  show 2 * arctan (1 / 10) + 2 * arctan (2 / 10) + 2 * arctan (3 / 10) ≤ π / 2
  have := arctan_lt_self (show (0 : ℝ) < 1 / 10 by norm_num)
  have := arctan_lt_self (show (0 : ℝ) < 2 / 10 by norm_num)
  have := arctan_lt_self (show (0 : ℝ) < 3 / 10 by norm_num)
  linarith [Real.pi_gt_three]
/-- Witness for pattern `P1`. -/
theorem witness_P1 : Admissible ![Ls1 0, Ls1 2, Ls1 3, Ls1 1] ![As1 2, As1 0, As1 1] ∧
    T ![As1 2, As1 0, As1 1] ≤ π / 2 ∧
    Optimal ![Ls1 0, Ls1 2, Ls1 3, Ls1 1] ![As1 2, As1 0, As1 1] ∧
    P1 ![Ls1 0, Ls1 2, Ls1 3, Ls1 1] ![As1 2, As1 0, As1 1] := by
  have hσ : Ls1 ∘ ⇑((Equiv.swap (1 : Fin 4) 3 * Equiv.swap 1 2 : Equiv.Perm (Fin 4))) = ![Ls1 0, Ls1 2, Ls1 3, Ls1 1] := by
    funext i; fin_cases i <;> simp [Equiv.swap_apply_def]
  have hτ : As1 ∘ ⇑((Equiv.swap (0 : Fin 3) 1 * Equiv.swap 0 2 : Equiv.Perm (Fin 3))) = ![As1 2, As1 0, As1 1] := by
    funext i; fin_cases i <;> simp [Equiv.swap_apply_def]
  have hT : As1 0 + As1 1 + As1 2 < π := by linarith [sum_As1, Real.pi_pos]
  have hL0 : 0 < Ls1 0 := by simp [Ls1]
  have hadm := admissible_sorted mono_Ls1 mono_As1 hL0 pos_As1 hT ((Equiv.swap (1 : Fin 4) 3 * Equiv.swap 1 2 : Equiv.Perm (Fin 4))) ((Equiv.swap (0 : Fin 3) 1 * Equiv.swap 0 2 : Equiv.Perm (Fin 3)))
  have hopt := n4_optimal_of_values mono_Ls1 mono_As1 hL0 pos_As1 hT ((Equiv.swap (1 : Fin 4) 3 * Equiv.swap 1 2 : Equiv.Perm (Fin 4))) ((Equiv.swap (0 : Fin 3) 1 * Equiv.swap 0 2 : Equiv.Perm (Fin 3)))
    (by rw [hσ, hτ])
    (by rw [hσ, hτ]; apply norm_le_of_normSq; rw [val_1_P2, val_1_P1]; norm_num)
    (by rw [hσ, hτ]; apply norm_le_of_normSq; rw [val_1_P3, val_1_P1]; norm_num)
  rw [hσ, hτ] at hadm hopt
  refine ⟨hadm, ?_, hopt, ?_⟩
  · unfold T; rw [(θ3 _).2.2]; show As1 2 + As1 0 + As1 1 ≤ π / 2; linarith [sum_As1]
  · show Ls1 0 < Ls1 1 ∧ Ls1 1 < Ls1 2 ∧ Ls1 2 < Ls1 3 ∧ As1 0 < As1 1 ∧ As1 1 < As1 2
    refine ⟨mono_Ls1 (by decide), mono_Ls1 (by decide), mono_Ls1 (by decide), mono_As1 (by decide), mono_As1 (by decide)⟩

def Ls2 : Fin 4 → ℝ := ![2, 3, 4, 5]
noncomputable def As2 : Fin 3 → ℝ := ![2 * arctan (1 / 10), 2 * arctan (2 / 10), 2 * arctan (4 / 10)]
lemma e_As2_0 : e (As2 0) = ⟨99 / 101, 20 / 101⟩ := by
  rw [show As2 0 = 2 * arctan (1 / 10) from rfl, e_two_arctan]; norm_num
lemma e_As2_1 : e (As2 1) = ⟨12 / 13, 5 / 13⟩ := by
  rw [show As2 1 = 2 * arctan (2 / 10) from rfl, e_two_arctan]; norm_num
lemma e_As2_2 : e (As2 2) = ⟨21 / 29, 20 / 29⟩ := by
  rw [show As2 2 = 2 * arctan (4 / 10) from rfl, e_two_arctan]; norm_num
lemma val_2_P1 : Complex.normSq (Z ![Ls2 0, Ls2 2, Ls2 3, Ls2 1] ![As2 2, As2 0, As2 1]) = 6336250 / 38077 := by
  rw [Z4]; simp [Ls2, Complex.normSq_apply, Complex.mul_re, Complex.mul_im, e_As2_0, e_As2_1, e_As2_2]; norm_num
lemma val_2_P2 : Complex.normSq (Z ![Ls2 0, Ls2 3, Ls2 2, Ls2 1] ![As2 2, As2 0, As2 1]) = 6337658 / 38077 := by
  rw [Z4]; simp [Ls2, Complex.normSq_apply, Complex.mul_re, Complex.mul_im, e_As2_0, e_As2_1, e_As2_2]; norm_num
lemma val_2_P3 : Complex.normSq (Z ![Ls2 0, Ls2 2, Ls2 3, Ls2 1] ![As2 1, As2 0, As2 2]) = 61300 / 377 := by
  rw [Z4]; simp [Ls2, Complex.normSq_apply, Complex.mul_re, Complex.mul_im, e_As2_0, e_As2_1, e_As2_2]; norm_num
lemma mono_Ls2 : StrictMono Ls2 := by
  refine Fin.strictMono_iff_lt_succ.2 fun i => ?_; fin_cases i <;> norm_num [Ls2]
lemma mono_As2 : StrictMono As2 := by
  refine Fin.strictMono_iff_lt_succ.2 fun i => ?_
  fin_cases i <;> norm_num [As2, arctan_lt_arctan_iff]
lemma pos_As2 : 0 < As2 0 := by simp [As2, arctan_pos]
lemma sum_As2 : As2 0 + As2 1 + As2 2 ≤ π / 2 := by
  show 2 * arctan (1 / 10) + 2 * arctan (2 / 10) + 2 * arctan (4 / 10) ≤ π / 2
  have := arctan_lt_self (show (0 : ℝ) < 1 / 10 by norm_num)
  have := arctan_lt_self (show (0 : ℝ) < 2 / 10 by norm_num)
  have := arctan_lt_self (show (0 : ℝ) < 4 / 10 by norm_num)
  linarith [Real.pi_gt_three]
/-- Witness for pattern `P2`. -/
theorem witness_P2 : Admissible ![Ls2 0, Ls2 3, Ls2 2, Ls2 1] ![As2 2, As2 0, As2 1] ∧
    T ![As2 2, As2 0, As2 1] ≤ π / 2 ∧
    Optimal ![Ls2 0, Ls2 3, Ls2 2, Ls2 1] ![As2 2, As2 0, As2 1] ∧
    P2 ![Ls2 0, Ls2 3, Ls2 2, Ls2 1] ![As2 2, As2 0, As2 1] := by
  have hσ : Ls2 ∘ ⇑(Equiv.swap (1 : Fin 4) 3) = ![Ls2 0, Ls2 3, Ls2 2, Ls2 1] := by
    funext i; fin_cases i <;> simp [Equiv.swap_apply_def]
  have hτ : As2 ∘ ⇑((Equiv.swap (0 : Fin 3) 1 * Equiv.swap 0 2 : Equiv.Perm (Fin 3))) = ![As2 2, As2 0, As2 1] := by
    funext i; fin_cases i <;> simp [Equiv.swap_apply_def]
  have hT : As2 0 + As2 1 + As2 2 < π := by linarith [sum_As2, Real.pi_pos]
  have hL0 : 0 < Ls2 0 := by simp [Ls2]
  have hadm := admissible_sorted mono_Ls2 mono_As2 hL0 pos_As2 hT (Equiv.swap (1 : Fin 4) 3) ((Equiv.swap (0 : Fin 3) 1 * Equiv.swap 0 2 : Equiv.Perm (Fin 3)))
  have hopt := n4_optimal_of_values mono_Ls2 mono_As2 hL0 pos_As2 hT (Equiv.swap (1 : Fin 4) 3) ((Equiv.swap (0 : Fin 3) 1 * Equiv.swap 0 2 : Equiv.Perm (Fin 3)))
    (by rw [hσ, hτ]; apply norm_le_of_normSq; rw [val_2_P1, val_2_P2]; norm_num)
    (by rw [hσ, hτ])
    (by rw [hσ, hτ]; apply norm_le_of_normSq; rw [val_2_P3, val_2_P2]; norm_num)
  rw [hσ, hτ] at hadm hopt
  refine ⟨hadm, ?_, hopt, ?_⟩
  · unfold T; rw [(θ3 _).2.2]; show As2 2 + As2 0 + As2 1 ≤ π / 2; linarith [sum_As2]
  · show Ls2 0 < Ls2 1 ∧ Ls2 1 < Ls2 2 ∧ Ls2 2 < Ls2 3 ∧ As2 0 < As2 1 ∧ As2 1 < As2 2
    refine ⟨mono_Ls2 (by decide), mono_Ls2 (by decide), mono_Ls2 (by decide), mono_As2 (by decide), mono_As2 (by decide)⟩

def Ls3 : Fin 4 → ℝ := ![8, 9, 10, 32]
noncomputable def As3 : Fin 3 → ℝ := ![2 * arctan (2 / 20), 2 * arctan (3 / 20), 2 * arctan (4 / 20)]
lemma e_As3_0 : e (As3 0) = ⟨99 / 101, 20 / 101⟩ := by
  rw [show As3 0 = 2 * arctan (2 / 20) from rfl, e_two_arctan]; norm_num
lemma e_As3_1 : e (As3 1) = ⟨391 / 409, 120 / 409⟩ := by
  rw [show As3 1 = 2 * arctan (3 / 20) from rfl, e_two_arctan]; norm_num
lemma e_As3_2 : e (As3 2) = ⟨12 / 13, 5 / 13⟩ := by
  rw [show As3 2 = 2 * arctan (4 / 20) from rfl, e_two_arctan]; norm_num
lemma val_3_P1 : Complex.normSq (Z ![Ls3 0, Ls3 2, Ls3 3, Ls3 1] ![As3 2, As3 0, As3 1]) = 1754738497 / 537017 := by
  rw [Z4]; simp [Ls3, Complex.normSq_apply, Complex.mul_re, Complex.mul_im, e_As3_0, e_As3_1, e_As3_2]; norm_num
lemma val_3_P2 : Complex.normSq (Z ![Ls3 0, Ls3 3, Ls3 2, Ls3 1] ![As3 2, As3 0, As3 1]) = 1756209593 / 537017 := by
  rw [Z4]; simp [Ls3, Complex.normSq_apply, Complex.mul_re, Complex.mul_im, e_As3_0, e_As3_1, e_As3_2]; norm_num
lemma val_3_P3 : Complex.normSq (Z ![Ls3 0, Ls3 2, Ls3 3, Ls3 1] ![As3 1, As3 0, As3 2]) = 1756357997 / 537017 := by
  rw [Z4]; simp [Ls3, Complex.normSq_apply, Complex.mul_re, Complex.mul_im, e_As3_0, e_As3_1, e_As3_2]; norm_num
lemma mono_Ls3 : StrictMono Ls3 := by
  refine Fin.strictMono_iff_lt_succ.2 fun i => ?_; fin_cases i <;> norm_num [Ls3]
lemma mono_As3 : StrictMono As3 := by
  refine Fin.strictMono_iff_lt_succ.2 fun i => ?_
  fin_cases i <;> norm_num [As3, arctan_lt_arctan_iff]
lemma pos_As3 : 0 < As3 0 := by simp [As3, arctan_pos]
lemma sum_As3 : As3 0 + As3 1 + As3 2 ≤ π / 2 := by
  show 2 * arctan (2 / 20) + 2 * arctan (3 / 20) + 2 * arctan (4 / 20) ≤ π / 2
  have := arctan_lt_self (show (0 : ℝ) < 2 / 20 by norm_num)
  have := arctan_lt_self (show (0 : ℝ) < 3 / 20 by norm_num)
  have := arctan_lt_self (show (0 : ℝ) < 4 / 20 by norm_num)
  linarith [Real.pi_gt_three]
/-- Witness for pattern `P3`. -/
theorem witness_P3 : Admissible ![Ls3 0, Ls3 2, Ls3 3, Ls3 1] ![As3 1, As3 0, As3 2] ∧
    T ![As3 1, As3 0, As3 2] ≤ π / 2 ∧
    Optimal ![Ls3 0, Ls3 2, Ls3 3, Ls3 1] ![As3 1, As3 0, As3 2] ∧
    P3 ![Ls3 0, Ls3 2, Ls3 3, Ls3 1] ![As3 1, As3 0, As3 2] := by
  have hσ : Ls3 ∘ ⇑((Equiv.swap (1 : Fin 4) 3 * Equiv.swap 1 2 : Equiv.Perm (Fin 4))) = ![Ls3 0, Ls3 2, Ls3 3, Ls3 1] := by
    funext i; fin_cases i <;> simp [Equiv.swap_apply_def]
  have hτ : As3 ∘ ⇑(Equiv.swap (0 : Fin 3) 1) = ![As3 1, As3 0, As3 2] := by
    funext i; fin_cases i <;> simp [Equiv.swap_apply_def]
  have hT : As3 0 + As3 1 + As3 2 < π := by linarith [sum_As3, Real.pi_pos]
  have hL0 : 0 < Ls3 0 := by simp [Ls3]
  have hadm := admissible_sorted mono_Ls3 mono_As3 hL0 pos_As3 hT ((Equiv.swap (1 : Fin 4) 3 * Equiv.swap 1 2 : Equiv.Perm (Fin 4))) (Equiv.swap (0 : Fin 3) 1)
  have hopt := n4_optimal_of_values mono_Ls3 mono_As3 hL0 pos_As3 hT ((Equiv.swap (1 : Fin 4) 3 * Equiv.swap 1 2 : Equiv.Perm (Fin 4))) (Equiv.swap (0 : Fin 3) 1)
    (by rw [hσ, hτ]; apply norm_le_of_normSq; rw [val_3_P1, val_3_P3]; norm_num)
    (by rw [hσ, hτ]; apply norm_le_of_normSq; rw [val_3_P2, val_3_P3]; norm_num)
    (by rw [hσ, hτ])
  rw [hσ, hτ] at hadm hopt
  refine ⟨hadm, ?_, hopt, ?_⟩
  · unfold T; rw [(θ3 _).2.2]; show As3 1 + As3 0 + As3 2 ≤ π / 2; linarith [sum_As3]
  · show Ls3 0 < Ls3 1 ∧ Ls3 1 < Ls3 2 ∧ Ls3 2 < Ls3 3 ∧ As3 0 < As3 1 ∧ As3 1 < As3 2
    refine ⟨mono_Ls3 (by decide), mono_Ls3 (by decide), mono_Ls3 (by decide), mono_As3 (by decide), mono_As3 (by decide)⟩

/-- **`a₄ = 3`.** With the shortest segment first, every optimum of four segments has one of the three patterns,
which are mutually exclusive, and each of them is optimal for some data with total turn at most `π/2`. -/
theorem a4_eq_three :
    (∀ (l : Fin 4 → ℝ) (a : Fin 3 → ℝ), Admissible l a → Optimal l a → (∀ j, j ≠ 0 → l 0 < l j) →
      P1 l a ∨ P2 l a ∨ P3 l a) ∧
    (∀ (l : Fin 4 → ℝ) (a : Fin 3 → ℝ), ¬ (P1 l a ∧ P2 l a) ∧ ¬ (P1 l a ∧ P3 l a) ∧ ¬ (P2 l a ∧ P3 l a)) ∧
    (∃ (l : Fin 4 → ℝ) (a : Fin 3 → ℝ), Admissible l a ∧ T a ≤ π / 2 ∧ Optimal l a ∧ P1 l a) ∧
    (∃ (l : Fin 4 → ℝ) (a : Fin 3 → ℝ), Admissible l a ∧ T a ≤ π / 2 ∧ Optimal l a ∧ P2 l a) ∧
    (∃ (l : Fin 4 → ℝ) (a : Fin 3 → ℝ), Admissible l a ∧ T a ≤ π / 2 ∧ Optimal l a ∧ P3 l a) := by
  refine ⟨fun l a h ho hm => n4_classify h ho hm, fun l a => ⟨?_, ?_, ?_⟩, ⟨_, _, witness_P1⟩, ⟨_, _, witness_P2⟩,
    ⟨_, _, witness_P3⟩⟩
  · rintro ⟨h1, h2⟩; unfold P1 P2 at *; linarith [h1.2.2.1, h2.2.2.1]
  · rintro ⟨h1, h3⟩; unfold P1 P3 at *; linarith [h1.2.2.2.2, h3.2.2.2.2]
  · rintro ⟨h2, h3⟩; unfold P2 P3 at *; linarith [h2.2.2.1, h3.2.2.1]

end Spans
