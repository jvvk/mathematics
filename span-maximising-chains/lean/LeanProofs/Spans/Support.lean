import LeanProofs.Spans.Moves

/-!
# Span-maximizing chains: the supporting direction and the exchange lemmas

Let `φ = arg Z` at an optimum. Every rearrangement has projection onto `φ` at most `‖Z‖`, with equality only for
the same displacement (Lemma 2.1). Swapping two lengths gives Lemma 2.2, swapping two adjacent turns Lemma 2.4.
-/

open Complex Finset Real

namespace Spans

variable {m : ℕ}

/-! ## Trigonometric helpers -/

lemma sin_pos_iff_of_abs_lt {x : ℝ} (h1 : -π < x) (h2 : x < π) : 0 < Real.sin x ↔ 0 < x := by
  constructor
  · intro hs; by_contra hx; push_neg at hx
    rcases hx.lt_or_eq with hx | hx
    · linarith [sin_neg_of_neg_of_neg_pi_lt hx h1]
    · rw [hx, Real.sin_zero] at hs; exact lt_irrefl _ hs
  · intro hx; exact sin_pos_of_pos_of_lt_pi hx h2

lemma sin_neg_iff_of_abs_lt {x : ℝ} (h1 : -π < x) (h2 : x < π) : Real.sin x < 0 ↔ x < 0 := by
  have := sin_pos_iff_of_abs_lt (x := -x) (by linarith) (by linarith)
  rw [Real.sin_neg] at this
  constructor
  · intro h; have := this.1 (by linarith); linarith
  · intro h; have := this.2 (by linarith); linarith

/-- On `[-π, π]`, a larger cosine means a smaller absolute value. -/
lemma cos_lt_cos_iff_abs {x y : ℝ} (hx : |x| ≤ π) (hy : |y| ≤ π) :
    Real.cos x < Real.cos y ↔ |y| < |x| := by
  rw [← Real.cos_abs x, ← Real.cos_abs y]
  constructor
  · intro h; by_contra h'; push_neg at h'
    rcases h'.lt_or_eq with h' | h'
    · linarith [cos_lt_cos_of_nonneg_of_le_pi (abs_nonneg x) hy h']
    · rw [h'] at h; exact lt_irrefl _ h
  · intro h; exact cos_lt_cos_of_nonneg_of_le_pi (abs_nonneg y) hx h

lemma e_mul_re (φ x : ℝ) : (e (-φ) * e x).re = Real.cos (x - φ) := by
  rw [← e_add, e_re]; ring_nf

lemma e_inj {x y : ℝ} (hx0 : 0 ≤ x) (hxπ : x ≤ π) (hy0 : 0 ≤ y) (hyπ : y ≤ π) (h : e x = e y) : x = y := by
  have := congrArg Complex.re h
  rw [e_re, e_re] at this
  exact injOn_cos ⟨hx0, hxπ⟩ ⟨hy0, hyπ⟩ this

/-! ## The direction of `Z` -/

section direction
variable {l : Fin (m + 1) → ℝ} {a : Fin m → ℝ} (h : Admissible l a)
include h

lemma θ_lt_pi {i : ℕ} (hi : i ≤ m) : θ a i < π := (θ_le_T h.apos hi).trans_lt h.Tlt

lemma T_pos (hm : 1 ≤ m) : 0 < T a := by
  have := θ_strictMono h.apos (i := 0) (k := m) (by omega) le_rfl
  rwa [θ_zero] at this

lemma Z_im_pos (hm : 1 ≤ m) : 0 < (Z l a).im := by
  unfold Z
  rw [Complex.im_sum]
  have hterm : ∀ i : Fin (m + 1), 0 ≤ ((l i : ℂ) * e (θ a i)).im := fun i => by
    rw [Complex.im_ofReal_mul, e_im]
    exact mul_nonneg (h.lpos i).le
      (sin_nonneg_of_nonneg_of_le_pi (θ_nonneg h.apos _) (θ_lt_pi h (by omega)).le)
  have h1 : 0 < ((l ⟨1, by omega⟩ : ℂ) * e (θ a 1)).im := by
    rw [Complex.im_ofReal_mul, e_im]
    have hθ : 0 < θ a 1 := by
      have := θ_strictMono h.apos (i := 0) (k := 1) (by omega) hm; rwa [θ_zero] at this
    exact mul_pos (h.lpos _) (sin_pos_of_pos_of_lt_pi hθ (θ_lt_pi h hm))
  calc 0 < ((l ⟨1, by omega⟩ : ℂ) * e (θ a 1)).im := h1
    _ ≤ ∑ i : Fin (m + 1), ((l i : ℂ) * e (θ a i)).im :=
      single_le_sum (f := fun i : Fin (m + 1) => ((l i : ℂ) * e (θ a i)).im) (fun i _ => hterm i)
        (mem_univ _)

lemma Z_ne_zero (hm : 1 ≤ m) : Z l a ≠ 0 := fun h0 => by
  have := Z_im_pos h hm; rw [h0, Complex.zero_im] at this; exact lt_irrefl _ this

lemma Z_polar : (‖Z l a‖ : ℂ) * e (arg (Z l a)) = Z l a := norm_mul_exp_arg_mul_I _

lemma arg_pos (hm : 1 ≤ m) : 0 < arg (Z l a) := by
  have h0 : 0 ≤ arg (Z l a) := arg_nonneg_iff.2 (Z_im_pos h hm).le
  rcases h0.lt_or_eq with h0 | h0
  · exact h0
  · have := (arg_eq_zero_iff.1 h0.symm).2
    linarith [Z_im_pos h hm]

lemma arg_lt_pi (hm : 1 ≤ m) : arg (Z l a) < π :=
  arg_lt_pi_iff.2 (Or.inr (Z_im_pos h hm).ne')

lemma arg_lt_T (hm : 1 ≤ m) : arg (Z l a) < T a := by
  -- the imaginary part of `Z e^{-iT}` is negative
  have hneg : (Z l a * e (-T a)).im < 0 := by
    unfold Z
    rw [sum_mul, Complex.im_sum]
    have hterm : ∀ i : Fin (m + 1), ((l i : ℂ) * e (θ a i) * e (-T a)).im ≤ 0 := fun i => by
      rw [mul_assoc, ← e_add, Complex.im_ofReal_mul, e_im]
      apply mul_nonpos_of_nonneg_of_nonpos (h.lpos i).le
      have h1 : θ a i - T a ≤ 0 := by linarith [θ_le_T h.apos (i := i) (by omega)]
      have h2 : -π < θ a i - T a := by linarith [θ_nonneg h.apos (i : ℕ), h.Tlt]
      rcases h1.lt_or_eq with h1 | h1
      · rw [show θ a i + -T a = θ a i - T a by ring]; exact (sin_neg_of_neg_of_neg_pi_lt h1 h2).le
      · rw [show θ a i + -T a = θ a i - T a by ring, h1, Real.sin_zero]
    have h0 : ((l 0 : ℂ) * e (θ a (0 : Fin (m + 1))) * e (-T a)).im < 0 := by
      rw [mul_assoc, ← e_add, Complex.im_ofReal_mul, e_im]
      simp only [Fin.val_zero, θ_zero, zero_add]
      rw [Real.sin_neg]
      have := sin_pos_of_pos_of_lt_pi (T_pos h hm) h.Tlt
      nlinarith [h.lpos 0]
    rw [← Finset.add_sum_erase _ _ (mem_univ (0 : Fin (m + 1)))]
    have := sum_nonpos fun i (_ : i ∈ univ.erase (0 : Fin (m + 1))) => hterm i
    linarith
  have hpol := Z_polar h
  rw [← hpol, mul_assoc, ← e_add, Complex.im_ofReal_mul, e_im] at hneg
  have hn : 0 < ‖Z l a‖ := norm_pos_iff.2 (Z_ne_zero h hm)
  have hs : Real.sin (arg (Z l a) + -T a) < 0 := by
    by_contra hc; push_neg at hc; nlinarith
  rw [sin_neg_iff_of_abs_lt (by linarith [arg_pos h hm, h.Tlt]) (by linarith [arg_lt_pi h hm, T_pos h hm])]
    at hs
  linarith

end direction

end Spans
