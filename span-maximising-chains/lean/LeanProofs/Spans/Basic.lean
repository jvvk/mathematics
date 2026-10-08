import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex
import Mathlib.Tactic

/-!
# Span-maximizing chains (MO 442949): the model

A chain has `m + 1` segments with lengths `l : Fin (m+1) → ℝ` and `m` turns `a : Fin m → ℝ`, all anticlockwise.
Segment `i` points in direction `θ a i = a 0 + ⋯ + a (i-1)`, and the span is `‖Z l a‖` with
`Z l a = ∑ l i · e^{i θ a i}`. An arrangement is *optimal* if no permutation of the lengths and of the turns gives a
larger span.
-/

open Complex Finset Real

namespace Spans

variable {m : ℕ}

/-- Turns extended by zero beyond the last one. -/
def ext (a : Fin m → ℝ) (j : ℕ) : ℝ := if h : j < m then a ⟨j, h⟩ else 0

/-- Direction of segment `i`: the sum of the first `i` turns. -/
def θ (a : Fin m → ℝ) (i : ℕ) : ℝ := ∑ j ∈ range i, ext a j

/-- Unit vector in direction `x`. -/
noncomputable def e (x : ℝ) : ℂ := exp ((x : ℂ) * I)

/-- The displacement of the chain. -/
noncomputable def Z (l : Fin (m + 1) → ℝ) (a : Fin m → ℝ) : ℂ := ∑ i : Fin (m + 1), (l i : ℂ) * e (θ a i)

/-- The total turn. -/
def T (a : Fin m → ℝ) : ℝ := θ a m

/-- Optimal: no rearrangement of the lengths and the turns has a larger span. -/
def Optimal (l : Fin (m + 1) → ℝ) (a : Fin m → ℝ) : Prop :=
  ∀ (σ : Equiv.Perm (Fin (m + 1))) (τ : Equiv.Perm (Fin m)), ‖Z (l ∘ σ) (a ∘ τ)‖ ≤ ‖Z l a‖

/-- Admissible data: distinct positive lengths, distinct positive turns, total turn below `π`. -/
structure Admissible (l : Fin (m + 1) → ℝ) (a : Fin m → ℝ) : Prop where
  lpos : ∀ i, 0 < l i
  linj : Function.Injective l
  apos : ∀ j, 0 < a j
  ainj : Function.Injective a
  Tlt : T a < π

/-! ## Elementary facts -/

lemma e_add (x y : ℝ) : e (x + y) = e x * e y := by
  unfold e; rw [← Complex.exp_add]; push_cast; ring_nf

lemma e_re (x : ℝ) : (e x).re = Real.cos x := by
  unfold e; rw [Complex.exp_ofReal_mul_I_re]

lemma e_im (x : ℝ) : (e x).im = Real.sin x := by
  unfold e; rw [Complex.exp_ofReal_mul_I_im]

lemma norm_e (x : ℝ) : ‖e x‖ = 1 := by unfold e; exact Complex.norm_exp_ofReal_mul_I x

lemma ext_nonneg {a : Fin m → ℝ} (ha : ∀ j, 0 < a j) (j : ℕ) : 0 ≤ ext a j := by
  unfold ext; split_ifs with h
  · exact (ha _).le
  · exact le_rfl

lemma θ_zero (a : Fin m → ℝ) : θ a 0 = 0 := by simp [θ]

lemma θ_succ (a : Fin m → ℝ) (i : ℕ) : θ a (i + 1) = θ a i + ext a i := by
  simp [θ, sum_range_succ]

lemma θ_mono {a : Fin m → ℝ} (ha : ∀ j, 0 < a j) {i k : ℕ} (hik : i ≤ k) : θ a i ≤ θ a k := by
  unfold θ
  exact sum_le_sum_of_subset_of_nonneg (range_mono hik) fun j _ _ => ext_nonneg ha j

lemma θ_strictMono {a : Fin m → ℝ} (ha : ∀ j, 0 < a j) {i k : ℕ} (hik : i < k) (hk : k ≤ m) :
    θ a i < θ a k := by
  have h1 : θ a (i + 1) ≤ θ a k := θ_mono ha hik
  have h2 : 0 < ext a i := by unfold ext; rw [dif_pos (by omega)]; exact ha _
  rw [θ_succ] at h1; linarith

lemma θ_nonneg {a : Fin m → ℝ} (ha : ∀ j, 0 < a j) (i : ℕ) : 0 ≤ θ a i := by
  have := θ_mono ha (Nat.zero_le i); rwa [θ_zero] at this

lemma θ_le_T {a : Fin m → ℝ} (ha : ∀ j, 0 < a j) {i : ℕ} (hi : i ≤ m) : θ a i ≤ T a := θ_mono ha hi

end Spans
